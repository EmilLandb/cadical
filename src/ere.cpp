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
    signed char tmp = marked (lit);
    if (tmp < 0) { // --> literal marked in opposite polarity
      invalid = true; // resolvent would be tautological
      break;
    }
    if (!tmp) // --> literal wasn't already added to resolvent
      clause.push_back (lit), size++;
  }

  if (size > static_cast<int64_t> (opts.ereclslim))
    invalid = true; // resolvent too long
  unmark (c);

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
void Internal::eager_redundancy_elimination () {
  if (!opts.ere)
    return;
  if (unsat)
    return;
  if (terminated_asynchronously ())
    return;

  assert (opts.ere);

  START_SIMPLIFIER (ere, ERE); // TODO: is this set up correctly?
  // TODO: some logic for when to run ERE (?)

  stats.erephases++;
  PHASE ("ere-phase", stats.erephases, "starting eager redundancy elimination");

  // set up occurrence lists
  init_occs ();
  for (const auto &c: clauses) {
    if (!c->garbage)
      for (const auto &lit : *c)
        occs (lit).push_back (c);
  }

  // eagerly compute resolvents
  const uint64_t ereocclim = opts.ereocclim;
  const int clslim = opts.ereclslim;

  for (int var = 1; var <= max_var; var++) {
    const uint64_t occsp = occs (var).size(); // number of positive occs
    const uint64_t occsn = occs (-var).size(); // number of negative occs
    if (occsp > ereocclim || occsn > ereocclim) {
       VERBOSE (3, "Occurrence lists for var %d have sizes %zu and %zu and will be skipped.",
         var, occsp, occsn);
       continue;
    }

    int svar = occsp < occsn ? var : -var; // determine shorter list
    for (const auto &c : occs (svar)) {
      if (c->garbage) // skip clauses that are up for deletion
        continue;
      if (c->size + 2 > clslim) // |c \ {svar}| > clslim
        continue;
      for (const auto &d : occs (-svar)) {
        if (d->garbage)
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

        // now look for redundant clauses in shortest
        for (auto &e : shortest) {
          if (e->garbage) // e is already up for deletion
            continue;
          if (e->size != res_size) // e cannot be equal
            continue;
          if (stats.erephases > 1 && !e->redundant) // TODO: If erephases > 1 we cannot find redundant original clauses (?)
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
  }

  assert (clause.empty());
  reset_occs();

  PHASE("ere-phase", stats.erephases,
        "eliminated %" PRId64 " clauses in %" PRId64 " resolutions",
        stats.ereredorig + stats.ereredlearnt, stats.ereres);

  STOP_SIMPLIFIER (ere, ERE); // TODO: Is this set up correctly?
  return;
}
} // namespace CaDiCaL
