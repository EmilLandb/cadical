#include "internal.hpp"
namespace CaDiCaL {

// Resolution of two clauses, assuming clause c cointans pivot,
// d contains -pivot, both non-tautological.
// Returns the size of the resolvent if the resolvent is non-tautological,
// and is not larger than eremaxresolvent
// Returns 0 if the resolvent is tautological or larger than ereclslim
int Internal::ere_resolve_clauses (Clause *c, int pivot, Clause *d) {
  START (ereres); // run-time profiling
  if (c->size > d->size) { // make sure d is not the smaller clause
    pivot = -pivot;
    swap (c,d);
  }

  assert (clause.empty ()); // resolvent will be computed into clause vector

  stats.ereres++;
  bool invalid = false;
  int64_t size = 0; // length of the computed resolvent

  // add non-pivot literals of c to the resolvent and mark them as added
  for (const auto &lit : *c) {
    if (lit == pivot)
      continue;
    assert (lit != -pivot); // c shouldn't be tautological
    mark (lit), clause.push_back (lit), size++;
  }

  // repeat for d, only add literals that are not marked
  for (const auto &lit : *d) {
    if (lit == -pivot)
      continue;
    assert (lit != pivot); // d shouldn't be tautological
    const signed char tmp = marked (lit);
    if (tmp < 0) { // --> literal marked in opposite polarity
      invalid = true; // resolvent would be tautological
      break;
    }
    if (!tmp) // --> literal wasn't already added to resolvent
      clause.push_back (lit), size++;
  }
  unmark (c);

  if (size > static_cast<int64_t> (opts.ereclslim))
    invalid = true; // resolvent too long

  if (invalid) {
    STOP (ereres);
    return 0; // 0 indicates invalid clause
  }
  if (!size) { // resolution proof of UNSAT
    learn_empty_clause (); // indicates UNSAT (?)
    STOP (ereres);
    return 0;
  }
  STOP (ereres);
  return size;
}

// Eagerly compute all resolvents and check for redundant clauses
bool Internal::eager_redundancy_elimination () {
  if (!opts.ere)
    return true;
  if (unsat)
    return true;
  if (terminated_asynchronously ())
    return true;

  assert (opts.ere);

  START_SIMPLIFIER (ere, ERE);

  SET_EFFORT_LIMIT (tick_limit, ere, true);

  stats.erephases++;
  PHASE ("ere-phase", stats.erephases, "starting eager redundancy elimination");

  // for counting up ticks
  int64_t &ticks = stats.ticks.ere;

  // set up occurrence lists
  init_occs ();
  for (const auto &c: clauses) {
	if (opts.ereirredonly && opts.ereirredonlyrem && c->redundant)
	  continue;
    if (!likely_to_be_kept_clause (c)) // not (irredundant or low glue)
      continue;
    if (!c->garbage)
      for (const auto &lit : *c)
        occs (lit).push_back (c);
  }

  // eagerly compute resolvents
  const uint64_t occlim = opts.ereocclim;
  const int clslim = opts.ereclslim;
  const int old = stats.ereredorig + stats.ereredlearnt;

  if (ere_next_var > max_var) // since elim removes variables
    ere_next_var = 1;
  const int start_var = ere_next_var;
  int var = ere_next_var;

  while (stats.ticks.ere < tick_limit) {
    ere_next_var = var; // store next var if effort limit is reached

    const uint64_t occsp = occs (var).size(); // number of positive occs
    const uint64_t occsn = occs (-var).size(); // number of negative occs
    if (occsp > occlim || occsn > occlim) {
       VERBOSE (3, "Occurrence lists for var %d have sizes %llu and %llu and will be skipped.",
         var, occsp, occsn);
       // Manual wrap-around for skipped vars
       if (var == max_var)
         var = 1;
       else
         var++;
       if (var == start_var)
         break;
       continue;
    }

    int svar = occsp < occsn ? var : -var; // determine shorter list

    ticks += 1 + cache_lines (occs (svar).size(), sizeof (Clause *)); // REVIEW: For occs (svar)

    for (const auto &c : occs (svar)) {
      ticks++; // REVIEW: Deref clause c data
      if (c->garbage) // skip clauses that are up for deletion
        continue;
      if (opts.ereirredonly && c->redundant)
        continue;
      if (c->size + 2 > clslim) // |c \ {svar}| > clslim
        continue;

      ticks += 1 + cache_lines (occs (-svar).size(), sizeof (Clause *)); // REVIEW: For occs (-svar)

      for (const auto &d : occs (-svar)) {
        ticks++; // REVIEW: Deref clause d data
        if (d->garbage)
          continue;
        if (opts.ereirredonly && d->redundant)
          continue;
        if (d->size + 2 > clslim)
          continue;

        // c and d both qualify for resolution
        const int res_size = ere_resolve_clauses (c, svar, d);
        if (!res_size) { // tautological, empty or too large
          clause.clear();
          continue;
        }

        // only delete redundancy if it is redundant or parents are both
        // irredundant
        bool res_learned = c->redundant || d->redundant;

        // Find the shortest occurrence list among the resolvents literals.
        // Also mark the literals for an easier redundancy check.
        stats.eretriedequ++;
        // ticks++; // REVIEW: vector<int> clause probably still hot from resolution?
        size_t min_len = occs (clause[0]).size ();
        int min_lit = clause[0];
        for (const auto &lit : clause) {
          size_t len = occs (lit).size ();
          if (len < min_len) {
            min_len = len;
            min_lit = lit;
          }
          mark (lit);
        }
        const Occs& shortest = occs (min_lit);

        ticks += 1 + cache_lines (shortest.size(), sizeof (Clause *)); // REVIEW: For occs (min_lit)

        // now look for redundant clauses in shortest
        for (auto &e : shortest) {
          ticks++; // REVIEW: Deref clause e data
          if (e->garbage) // e is already up for deletion
            continue;
          if (e->size != res_size) // e cannot be equal
            continue;
		  if (opts.ereirredonlyrem && e->redundant) // REVIEW: Don't remove learnt clauses
			continue;
		  else if (opts.ereredonlyrem && !e->redundant) // REVIEW: Only remove learnt clauses
			continue;
          if (res_learned && !e->redundant) // e cannot be removed
            continue;
          bool redundant = true; // e may be redundant

          // check whether e is equal to the resolvent
          for (const auto &lit : *e) {
            if (marked (lit) <= 0) { // lit is in e but not in resolvent
              redundant = false;
              break;
            }
          }
          if (redundant) {
            LOG (e, "found");
            LOG (c, "by resolution of");
            LOG (d, "and");
            LOG ("on %d", var);
            if (e->redundant)
              stats.ereredlearnt++;
            else
              stats.ereredorig++;
            mark_garbage (e);
            break; // Assuming e only occurs once
          }
        }
        // clean up
        for (const auto &lit : clause) {
          unmark (lit);
        }
        clause.clear();
      }
    }
    // Increment var with wrap-around
    if (var == max_var)
      var = 1;
    else
      var++;
    // Stop if a full cycle is completed
    if (var == start_var)
      break;
  }

  assert (clause.empty());
  reset_occs();
  VERBOSE (3, "Went from var %d to var %d", start_var, ere_next_var);
  PHASE("ere-phase", stats.erephases,
        "eliminated %" PRId64 " clauses in %" PRId64 " resolutions",
        stats.ereredorig + stats.ereredlearnt, stats.ereres);

  STOP_SIMPLIFIER (ere, ERE);
  report ('E', old == stats.ereredorig + stats.ereredlearnt);
  return true;
}
} // namespace CaDiCaL
