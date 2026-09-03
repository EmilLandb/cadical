#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// In incremental solving after a first call to 'solve' has finished and
// before calling the internal 'solve' again incrementally we have to
// restore clauses which have the negation of a literal as a witness literal
// on the extension stack, which was added as original literal in a new
// clause or in an assumption.  This procedure has to be applied
// recursively, i.e., the literals of restored clauses are treated in the
// same way as literals of a new original clause.
//
// To figure out whether literals are such witnesses we have a 'witness'
// bit for each external literal, which is set in 'block', 'elim', and
// 'decompose' if a clause is pushed on the extension stack.  The witness
// bits are recomputed after restoring clauses.
//
// We further mark in the external solver newly internalized external
// literals in 'add' and 'assume' since the last call to 'solve' as tainted
// if they occur negated as a witness literal on the extension stack.  Then
// we go through the extension stack and restore all clauses which have a
// tainted literal (and its negation a marked as witness).
//
// Since the API contract disallows to call 'val' and 'failed' in an
// 'UNKNOWN' state. We do not have to internalize literals there.
//
// In order to have tainted literals accepted by the internal solver they
// have to be active and thus we might need to 'reactivate' them before
// restoring clauses if they are inactive. In case they have completely
// been eliminated and removed from the internal solver in 'compact', then
// we just use a new internal variable.  This is performed in 'internalize'
// during marking external literals as tainted.
//
// To check that this approach is correct the external solver can maintain a
// stack of original clauses and current assumptions both in terms of
// external literals.  Whenever 'solve' determines that the current
// incremental call is satisfiable we check that the (extended) witness does
// satisfy the saved original clauses, as well as all the assumptions. To
// enable these checks set 'opts.check' as well as 'opts.checkwitness' and
// 'opts.checkassumptions' all to 'true'.  The model based tester actually
// prefers to enable the 'opts.check' option and the other two are 'true' by
// default anyhow.
//
// See our SAT'19 paper [FazekasBiereScholl-SAT'19] for more details.

/*------------------------------------------------------------------------*/

void External::restore_clause (const vector<int>::const_iterator &begin,
                               const vector<int>::const_iterator &end,
                               const int64_t id) {
  LOG (begin, end, "restoring external clause[%" PRId64 "]", id);
  assert (eclause.empty ());
  assert (id);
  for (auto p = begin; p != end; p++) {
    eclause.push_back (*p);
    if (internal->proof && internal->lrat) {
      const auto &elit = *p;
      unsigned eidx = (elit > 0) + 2u * (unsigned) abs (elit);
      assert ((size_t) eidx < ext_units.size ());
      const int64_t id = ext_units[eidx];
      bool added = ext_flags[abs (elit)];
      if (id && !added) {
        ext_flags[abs (elit)] = true;
        internal->lrat_chain.push_back (id);
      }
    }
    int ilit = internalize (*p);
    internal->add_original_lit (ilit), internal->stats.restored_literals++;
  }
  if (internal->proof && internal->lrat) {
    for (const auto &elit : eclause) {
      ext_flags[abs (elit)] = false;
    }
  }
  internal->finish_added_clause_with_id (id, true);
  eclause.clear ();
  internal->stats.restored_clauses++;
}

// TODO: Rather do one restore_clause (int * begin, int * end, ...)
// that both can use 
void External::restore_shared_clause (SharedClause *sc) {
  LOG ("restoring external shared clause[%" PRId64 "]", sc->id);
  
  assert (eclause.empty ());
  assert (sc->id);
  assert (sc->stale);

  for (const int *p = sc->elits; *p; ++p) {
    eclause.push_back (*p);
    if (internal->proof && internal->lrat) {
      const auto &elit = *p;
      unsigned eidx = (elit > 0) + 2u * (unsigned) abs (elit);
      assert ((size_t) eidx < ext_units.size ());
      const int64_t id = ext_units[eidx];
      bool added = ext_flags[abs (elit)];
      if (id && !added) {
        ext_flags[abs (elit)] = true;
        internal->lrat_chain.push_back (id);
      }
    }
    int ilit = internalize (*p);
    internal->add_original_lit (ilit), internal->stats.restored_literals++;
  }
  if (internal->proof && internal->lrat) {
    for (const auto &elit : eclause) {
      ext_flags[abs (elit)] = false;
    }
  }
  internal->finish_added_clause_with_id (sc->id, true);
  eclause.clear ();
  internal->stats.restored_clauses++;
}

/*------------------------------------------------------------------------*/
// Compacting the witness_order stack
void External::compact_witness_order () {
  
  VERBOSE (3, "compacting witness order stack of size %zu", 
           witness_order.size ());

  auto begin = witness_order.begin ();
  auto end = witness_order.end ();
  auto q = begin;

  for (auto p = begin; p != end; ++p) {
    const int ewit = *p;
    
    // Remove witness entry if tainted
    if (marked (tainted, -ewit))
      continue;

    *q++ = ewit;
  }
  const size_t old_size = witness_order.size ();
  witness_order.resize (q - begin);
  internal->stats.restore_compacted += (int64_t) old_size - witness_order.size ();
  internal->stats.restore_seen_bytes += old_size;
  internal->stats.restore_total_bytes += old_size;
  VERBOSE (3, "finished compacting with size %zu", 
           witness_order.size ());
}

// Process one witness stack. I.e. restore all clauses that are not flushed.
void External::restore_clauses (unsigned uwit, RestoreStats &clauses) {

  VERBOSE (3, "restoring all clauses on witness stack %u (ulit) of size %zu", 
           uwit, witness_stacks[uwit].size ());

  vector<int> &stack = witness_stacks[uwit];
  auto p = stack.begin ();
  auto end_of_stack = stack.end ();
  // 0 idu idl 0 l1 l2 ... lk 0 next clause
  // ^
  LOG (stack, "witness_stack: ");
  while (p != end_of_stack) {
    assert (!*p); // p is on '0' 
    p++; // now on idu
    clauses.weakened++;
    // copy the id of the clause
    const int64_t id = ((int64_t) (*p) << 32) + (int64_t) *(p + 1);
    int satisfied = 0;
    if (id) {
      LOG ("id is %" PRId64, id);
      p += 3; // now on the first literal after idu idl 0 

      auto begin = p;
      // now p is on the first literal of the clause, and we go to the next '0'
      while (p != end_of_stack && *p) { 
        if (!satisfied && fixed (*p) > 0)
          satisfied = *p;
        ++p;
      }
      if (satisfied && !internal->opts.restoreflush) {
        LOG (begin, p, "forced to not remove %d satisfied",
             satisfied);
        satisfied = 0;
      } 

      if (satisfied) {
        LOG (begin, p, 
               "flushing implied %s clause satisfied by %d from extension stack", 
               id ? "" : "dummy", satisfied);
          clauses.satisfied++;
      } else {
        clauses.restored++;
        if (id)
          restore_clause (begin, p, id); // Might taint literals 
      }
    } else {
      LOG ("shared clause detected");
      // 0 0 0 ptr_u ptr_l
      //   ^         
      const uintptr_t ptr = (static_cast<uintptr_t> (*(p + 2)) << 32) | 
                             static_cast<uint32_t> (*(p + 3));
      SharedClause *sc = reinterpret_cast<SharedClause*> (ptr);
      if (!sc->stale) {
        // check root level satisfaction
        for (int *p = sc->elits; *p; ++p) {
          if (fixed (*p) > 0) {
            satisfied = *p;
            break;
          }
        }
        // The clause is definitely stale now (restore or flush)
        sc->stale = true;  
        // stats and restoring/flushing
        if (!satisfied) {
          restore_shared_clause (sc);
          clauses.restored++;
        } else if (satisfied && !internal->opts.restoreflush)
            LOG ("forced to not remove %d satsfied shared clause", satisfied);
        else {
          LOG ("flushing implied shared clause satisfied by %d "
               "with %d active backlinks", satisfied, sc->backlinks);
          clauses.satisfied++;
        }
      } else
        LOG ("shared clause was already stale.");
      assert (sc->backlinks > 0);
      if (--sc->backlinks == 0) { // This was the last dummy clause. Free now.
        LOG ("Now no dummy clauses connected. Deleting shared clause...");
        delete[] (char *) sc;
      }
      p += 4; // now on the '0' after the dummy clause
    }
    // p is now on either on the (dummy) clause-terminating 0, 
    // or at end_of_stack if this is the final clause
    clauses.removed++;
  }
  clauses.seenbytes += sizeof (int) * stack.size ();
  stack.clear ();
}

// Propagate tainted literals and restore all clauses necessary 
void External::propagate_tainting (RestoreStats &clauses) {
  while (!tainted_stack.empty ()) {
    LOG (tainted_stack, "tainted_stack: ");
    const int ewit = -tainted_stack.back ();
    assert (marked (tainted, -ewit));

    const unsigned uwit = elit2ulit (ewit);
    tainted_stack.pop_back ();
    
    LOG ("restoring clauses with witness %d", ewit);
    restore_clauses (uwit, clauses);
    unmark (witness, ewit);
  }
  // Now we could remove entries from witness order which would result in a 
  // scan of the full witness_order stack (O(#clauses on stack)).
  // Hypothesis: We can also just ignore it and accept a longer witness_order
  // stack when we call extend. It should still be correct.

  // "resize" witness vector  
  while (!witness.empty () && !witness.back ())
    witness.pop_back ();
}

void External::restore_all (RestoreStats &clauses) {
  assert (internal->opts.restoreall == 2);
  LOG ("restoring all clauses");
  for (unsigned uwit = 1; uwit < witness_stacks.size (); ++uwit) {
    if (witness_stacks[uwit].empty ())
      continue;
    restore_clauses (uwit, clauses);
  }
  witness.clear (); // There should be no more clauses left on the stacks
  witness_order.clear ();
}

void External::restore () {
  START (restore);
  internal->stats.restorations++;

  RestoreStats clauses = {};

  if (internal->opts.restoreall && tainted.empty ())
    PHASE ("restore", internal->stats.restorations,
           "forced to restore all clauses");

#ifndef QUIET
  {
    unsigned numtainted = 0;
    for (const auto b : tainted)
      if (b)
        numtainted++;

    PHASE ("restore", internal->stats.restorations,
           "starting with %u tainted literals %.0f%%", numtainted,
           percent (numtainted, 2u * max_var));
    LOG ("tainted_stack size = %zu", tainted_stack.size ());
  }
#endif

  if (internal->opts.restoreall == 2) {
    restore_all (clauses);
  } 
  else if (!tainted.empty ()) {
    
    for (const auto &s : witness_stacks)
      clauses.totalbytes += s.size () * sizeof (int);

    propagate_tainting (clauses);

    if (internal->opts.restorecompact)
      compact_witness_order ();

    internal->stats.restore_total_bytes += clauses.totalbytes;
    internal->stats.restore_seen_bytes += clauses.seenbytes;
  }

#ifndef QUIET
  if (clauses.satisfied)
    PHASE ("restore", internal->stats.restorations,
           "removed %" PRId64 " satisfied %.0f%% of %" PRId64
           " weakened clauses",
           clauses.satisfied, percent (clauses.satisfied, clauses.weakened),
           clauses.weakened);
  else
    PHASE ("restore", internal->stats.restorations,
           "no satisfied clause removed out of %" PRId64
           " weakened clauses",
           clauses.weakened);

  if (clauses.restored)
    PHASE ("restore", internal->stats.restorations,
           "restored %" PRId64 " clauses %.0f%% out of %" PRId64
           " weakened clauses",
           clauses.restored, percent (clauses.restored, clauses.weakened),
           clauses.weakened);
  else
    PHASE ("restore", internal->stats.restorations,
           "no clause restored out of %" PRId64 " weakened clauses",
           clauses.weakened);
  {
    unsigned numtainted = 0;
    for (const auto &b : tainted)
      if (b)
        numtainted++;

    PHASE ("restore", internal->stats.restorations,
           "finishing with %u tainted literals %.0f%%", numtainted,
           percent (numtainted, 2u * max_var));
  }
#endif
  tainted.clear ();
  STOP (restore);
}

/*------------------------------------------------------------------------*/
/*
void External::restore_clauses () {

  assert (internal->opts.restoreall == 2 || !tainted.empty ());

  START (restore);
  internal->stats.restorations++;

  struct {
    int64_t weakened, satisfied, restored, removed;
  } clauses;
  memset (&clauses, 0, sizeof clauses);

  if (internal->opts.restoreall && tainted.empty ())
    PHASE ("restore", internal->stats.restorations,
           "forced to restore all clauses");

#ifndef QUIET
  {
    unsigned numtainted = 0;
    for (const auto b : tainted)
      if (b)
        numtainted++;

    PHASE ("restore", internal->stats.restorations,
           "starting with %u tainted literals %.0f%%", numtainted,
           percent (numtainted, 2u * max_var));
  }
#endif

  auto end_of_extension = extension.end ();
  auto p = extension.begin (), q = p;

  // Go over all witness labelled clauses on the extension stack, restore
  // those necessary, remove restored and flush satisfied clauses.
  //
  while (p != end_of_extension) {

    clauses.weakened++;

    assert (!*p);
    const auto saved = q; // Save old start.
    *q++ = *p++;          // Copy zero '0'.

    // Copy witness part and try to find a tainted witness literal in it.
    //
    int tlit = 0; // Negation tainted.
    int elit;
    //
    assert (p != end_of_extension);
    //
    while ((elit = *q++ = *p++)) {

      if (marked (tainted, -elit)) {
        tlit = elit;
        LOG ("negation of witness literal %d tainted", tlit);
      }

      assert (p != end_of_extension);
    }

    // now copy the id of the clause
    const int64_t id = ((int64_t) (*p) << 32) + (int64_t) *(p + 1);
    LOG ("id is %" PRId64, id);
    *q++ = *p++;
    *q++ = *p++;
    assert (id);
    assert (!*p);
    *q++ = *p++;

    // Now find 'end_of_clause' (clause starts at 'p') and at the same time
    // figure out whether the clause is actually root level satisfied.
    //
    int satisfied = 0;
    auto end_of_clause = p;
    while (end_of_clause != end_of_extension && (elit = *end_of_clause)) {
      if (!satisfied && fixed (elit) > 0)
        satisfied = elit;
      end_of_clause++;
    }
    assert (id);

    // Do not apply our 'FLUSH' rule to remove satisfied (implied) clauses
    // if the corresponding option is set simply by resetting 'satisfied'.
    //
    if (satisfied && !internal->opts.restoreflush) {
      LOG (p, end_of_clause, "forced to not remove %d satisfied",
           satisfied);
      satisfied = 0;
    }

    if (satisfied || tlit || internal->opts.restoreall) {

      if (satisfied) {
        LOG (p, end_of_clause,
             "flushing implied clause satisfied by %d from extension stack",
             satisfied);
        clauses.satisfied++;
      } else {
        restore_clause (p, end_of_clause, id); // Might taint literals.
        clauses.restored++;
      }

      clauses.removed++;
      p = end_of_clause;
      q = saved;

    } else {

      LOG (p, end_of_clause, "keeping clause on extension stack");

      while (p != end_of_clause) // Copy clause too.
        *q++ = *p++;
    }
  }

  extension.resize (q - extension.begin ());
  shrink_vector (extension);

#ifndef QUIET
  if (clauses.satisfied)
    PHASE ("restore", internal->stats.restorations,
           "removed %" PRId64 " satisfied %.0f%% of %" PRId64
           " weakened clauses",
           clauses.satisfied, percent (clauses.satisfied, clauses.weakened),
           clauses.weakened);
  else
    PHASE ("restore", internal->stats.restorations,
           "no satisfied clause removed out of %" PRId64
           " weakened clauses",
           clauses.weakened);

  if (clauses.restored)
    PHASE ("restore", internal->stats.restorations,
           "restored %" PRId64 " clauses %.0f%% out of %" PRId64
           " weakened clauses",
           clauses.restored, percent (clauses.restored, clauses.weakened),
           clauses.weakened);
  else
    PHASE ("restore", internal->stats.restorations,
           "no clause restored out of %" PRId64 " weakened clauses",
           clauses.weakened);
  {
    unsigned numtainted = 0;
    for (const auto &b : tainted)
      if (b)
        numtainted++;

    PHASE ("restore", internal->stats.restorations,
           "finishing with %u tainted literals %.0f%%", numtainted,
           percent (numtainted, 2u * max_var));
  }

#endif
  LOG ("extension stack clean");
  tainted.clear ();

  // Finally recompute the witness bits.
  //
  witness.clear ();
  const auto begin_of_extension = extension.begin ();
  p = extension.end ();
  while (p != begin_of_extension) {
    while (*--p)
      assert (p != begin_of_extension);
    int elit;
    assert (p != begin_of_extension);
    --p;
    assert (p != begin_of_extension);
    assert (*p || *(p - 1));
    --p;
    assert (p != begin_of_extension);
    assert (!*p);
    --p;
    assert (p != begin_of_extension);
    while ((elit = *--p)) {
      mark (witness, elit);
      assert (p != begin_of_extension);
    }
  }

  STOP (restore);
}
*/
} // namespace CaDiCaL
