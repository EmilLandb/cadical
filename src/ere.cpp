#include "internal.hpp"
namespace CaDiCaL {
// ---------------------------------------------------------------------------------------------------------------------
typedef vector<uint16_t> Sigs; // Signature list
vector<Sigs> sigtab;

void Internal::ere_init_sigs_and_occs () {
  if (sigtab.size () < 2 * vsize)
    sigtab.resize (2 * vsize, Sigs ());
  init_occs ();
  LOG ("initialized signature lists and occurrence lists");
}

void Internal::ere_reset_sigs_and_occs () {
  assert (!sigtab.empty ());
  erase_vector (sigtab);
  reset_occs ();
  LOG ("reset signature lists and occurrence lists");
}

void Internal::ere_fill_sigs_and_occs () {
  START (eresigotab);
  for (auto &c : clauses) { // sort, compute signature, add to sigoccs
    if (c->size == 2) // skip binary clauses
      continue;
    if (!likely_to_be_kept_clause (c)) // not (irredundant or low glue)
      continue;
    if (c->garbage)
      continue;
    int sig = 0;
    for (const auto &lit : *c) { // compute signature
      sig |= (1UL << ((lit) & 0x0000000F));
    }
    for (const auto &lit : *c) { // add to sigs and occs
	  sigtab[vlit (lit)].push_back(sig); // add signature to signatures
	  occs (lit).push_back (c); // add clause to occurrence lists
    }
  }
  STOP (eresigotab);
}
// ---------------------------------------------------------------------------------------------------------------------

// Resolution of two clauses, assuming clause c cointans pivot,
// d contains -pivot, both non-tautological.
// Returns the size of the resolvent if the resolvent is non-tautological,
// and is not larger than eremaxresolvent
// Returns 0 if the resolvent is tautological or larger than ereclslim
int Internal::ere_resolve_clauses (Clause *c, int pivot, Clause *d, int &sharedlit, int32_t &sig) {
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
	sig |= (1UL << ((lit) & 0x0000000F));
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
    } else if (!tmp) { // --> literal wasn't already added to resolvent
		sig |= (1UL << ((lit) & 0x0000000F));
		clause.push_back (lit), size++;
	}
    else { // literal occurs in both c and d
       sharedlit = lit;
    }
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

  SET_EFFORT_LIMIT (tick_limit, ere, true);

  START_SIMPLIFIER (ere, ERE);

  stats.erephases++;
  PHASE ("ere-phase", stats.erephases, "starting eager redundancy elimination");

  // for counting up ticks
  int64_t &ticks = stats.ticks.ere;

  // set up occurrence lists
  ticks += 1 + cache_lines (clauses.size (), sizeof (Clause *)); // REVIEW: Should i include building the occs?

  clear_watches ();
  ere_init_sigs_and_occs ();
  ere_fill_sigs_and_occs ();

  // eagerly compute resolvents
  const uint64_t occlim = opts.ereocclim;
  const int clslim = opts.ereclslim;
  const int old = stats.ereredorig + stats.ereredlearnt;

  if (ere_next_var > max_var) // since elim removes variables
    ere_next_var = 1;
  const int start_var = ere_next_var;
  int var = ere_next_var;

  while (stats.ticks.ere < tick_limit) {
    ere_next_var = var; // store next var for when effort limit is reached

	// REVIEW: Skip if var is not marked for subsumption
	if ((opts.eremarkedonly && !marked_subsume (var)) || !active (var)) { // if var is inactive go next
	  if (var == max_var)
	    var = 1;
	  else
	    var++;
	  if (var == start_var) {
        stats.erefullrotations++;
        break;
      }
      continue;
	}

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
       if (var == start_var) {
        stats.erefullrotations++;
        break;
      }
       continue;
    }

    int svar = occsp < occsn ? var : -var; // determine shorter list

    ticks += 1 + cache_lines (occs (svar).size(), sizeof (Clause *)); // REVIEW: For occs (svar)

    for (const auto &c : occs (svar)) {
	  if (!(stats.ticks.ere < tick_limit))
	    break;
      ticks++; // REVIEW: Deref clause c data
      if (c->garbage) // skip clauses that are up for deletion
        continue;
      if (opts.ereirredonly && c->redundant)
        continue;
      if (c->size + 2 > clslim) // |c \ {svar}| > clslim
        continue;

      ticks += 1 + cache_lines (occs (-svar).size(), sizeof (Clause *)); // REVIEW: For occs (-svar)

      for (const auto &d : occs (-svar)) {
        if (!(stats.ticks.ere < tick_limit)) {
          // early clean up
          for (const auto &lit : clause) {
            unmark (lit);
          }
          clause.clear();
	      break;
        }
        ticks++; // REVIEW: Deref clause d data
        if (d->garbage)
          continue;
        if (opts.ereirredonly && d->redundant)
          continue;
        if (d->size + 2 > clslim)
          continue;

        // c and d both qualify for resolution
        int sharedlit = 0; // REVIEW: for counting antecedents that share a literal
		int32_t res_sig = 0;
        ticks += 20; // REVIEW: some ticks for ere_resolve_clauses ? (Takes up ~ half of ere runtime)
        const int res_size = ere_resolve_clauses (c, svar, d, sharedlit, res_sig);
        if (!res_size) { // tautological, empty or too large
          clause.clear();
          continue;
        }

        // only delete equivalent clause if it is redundant (learnt) or parents are both
        // irredundant
        bool res_learnt = c->redundant || d->redundant;

        // Find the shortest occurrence list among the resolvents literals.
        // Also mark the literals for an easier redundancy check.
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
		const Sigs& shortest_sigs = sigtab[vlit (min_lit)];
        ticks += 1 + cache_lines(min_len, sizeof(uint16_t)); //  accessing shortest_sigs

        // now look for redundant clauses in shortest
        for (size_t i = 0; i < min_len; ++i) { // need index for finding the corresponding clause
          if (!(stats.ticks.ere < tick_limit))
	        break;
          stats.eretriedequ++;
		  // some literal that isn't in 'e' is in resolvent => resolvent can't subset of 'e'
		  if (res_sig & ~shortest_sigs[i]) {
            stats.erefiltered++;
			continue;
		  }
          ticks++; // REVIEW: Deref clause e data
		  auto &e = shortest[i];
          if (e->garbage) // e is already up for deletion
            continue;
          if (res_learnt && !e->redundant) // e cannot be removed
            continue;
          if (e->id == c->id || e->id == d->id) // for now without selfsubsumption. Without this bad things may happen
            continue;
          signed char redundant = 1; // e may be redundant, > 0 marks equivalent, < 0 marks subsumed

          // check whether 'e' is subsumed by the resolvent
          if (opts.erebackward && e->size > res_size) {
            LOG (e, "trying to subsume");
            LOG (clause, "with resolvent");
            int sharedlits = 0; // number of lits in resolvent that are also in 'e'
            for (const auto &lit : *e) {
              if (marked (lit) > 0)
                sharedlits++;
              else if (marked (lit) < 0) {
                 redundant = 0;
                 break;
              }
            }
            if (redundant && sharedlits == res_size) {
                redundant = -1;
            } else
                redundant = 0;
          } else if (e->size == res_size) { // check whether 'e' is equivalent to the resolvent
            for (const auto &lit : *e) {
              if (marked (lit) <= 0) { // lit is in e but not in resolvent
                redundant = 0;
                break;
              }
            }
          } else // cannot be subsumed or equivalent but 'redundant' wasn't set to false in this case
              continue;
          if (redundant) {
            if (redundant < 0) // found by subsumption
              LOG (e, "found subsumed");
            else
              LOG (e, "found equivalent");
            LOG (c, "by resolution of");
            LOG (d, "and");
            LOG ("on %d", var);
            if (e->redundant) {
              if (redundant < 0)
                stats.eresublearnt++;
              else
                stats.ereredlearnt++;
              if (sharedlit)
                stats.eresharedlit++; // antecedents shared at least one literal
            }
            else if (redundant < 0)
              stats.eresuborig++;
            else
              stats.ereredorig++;
            mark_garbage (e);
            if (!opts.erebackward) // We can stop, when not subsuming, assuming there are no duplicate clauses
              break;
          }
        }

        // TODO: This is still buggy (and also incomplete)
        // check for self-subsumtion. At this point all literals in the resolvent are marked.
		/*
        if (opts.ereselfsub) {
          bool cselfsub = false;
          if (c->size > res_size) {
            int sharedlits = 0; // number of literals of resolvent that are also in c
            for (const auto &lit : *c) {
              if (marked (lit) > 0) // lit is also in resolvent
                sharedlits++;
              else if (marked (lit) < 0) // lit is in resolvent in opposite polarity --> c can't be subsumed
                break;
            }
            if (sharedlits == res_size) { // all of the resolvents literals are also in c
              LOG (c, "self subsumed");
              LOG (clause, "by resolvent");
              stats.ereselfsub++;
              cselfsub = true;
              assert (lrat_chain.empty ());
              if (lrat) { // add antecedents to LRAT chain
                lrat_chain.push_back (c->id);
                lrat_chain.push_back (d->id);
              }
              new_resolved_irredundant_clause ();
              if (lrat) {
                lrat_chain.clear ();
              }
              mark_garbage (c);
            }
          }
        }
		*/
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
    if (var == start_var) {
      stats.erefullrotations++;
      break;
    }
  }

  assert (clause.empty());
  ere_reset_sigs_and_occs ();
  init_watches ();
  connect_watches ();
  VERBOSE (1, "ERE found %d redundancies", stats.ereredorig + stats.ereredlearnt - old); // TODO: remove after checking
  VERBOSE (3, "Went from var %d to var %d", start_var, ere_next_var);
  PHASE("ere-phase", stats.erephases,
        "eliminated %" PRId64 " clauses in %" PRId64 " resolutions",
        stats.ereredorig + stats.ereredlearnt, stats.ereres);

  STOP_SIMPLIFIER (ere, ERE);
  report ('E', old == stats.ereredorig + stats.ereredlearnt);
  return true;
}
} // namespace CaDiCaL
