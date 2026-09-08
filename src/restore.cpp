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
// Unsigned version of marked, mark and unmark
static bool u_marked (const vector<bool> &map, unsigned ulit) {
  return ulit < map.size () ? map[ulit] : false;
}

static void u_mark (vector<bool> &map, unsigned ulit) {
  if (ulit >= map.size ())
    map.resize (ulit + 1, false);
  map[ulit] = true;
}

static void u_unmark (vector<bool> &map, unsigned ulit) {
  if (ulit < map.size ())
    map[ulit] = false;
}
/*------------------------------------------------------------------------*/  

void External::set_restore_start (unsigned ulit, uint32_t timestamp) {
  if (restore_start.size () <= ulit)
    restore_start.resize (ulit + 1, 0);

  restore_start[ulit] = timestamp;
}

uint32_t External::get_restore_start (unsigned ulit) const {
  if (restore_start.size () <= ulit)
    return 0;
  return restore_start[ulit];
}

void External::schedule (unsigned ulit, uint32_t timestamp) {
  const uint32_t old = get_restore_start (ulit);
  if (!old) {
    set_restore_start (ulit, timestamp);
    tainted_heap.push_back (ulit);
  } else if (timestamp < old) {
    set_restore_start (ulit, timestamp);
    tainted_heap.update (ulit);
  }
}

void External::decide_scheduling (int elit, uint32_t timestamp) {
  const unsigned uwit = elit2ulit (-elit); // wit. that could need restoration

  if (!u_marked (witness, uwit)) // No clause with corresp. witness
    return;
  if (u_marked (processed, uwit)) // Already restored
    return;

  schedule (uwit, timestamp + 1);
}

void External::restore_clause (const vector<int>::const_iterator &begin,
                               const vector<int>::const_iterator &end,
                               const int64_t id, const uint32_t timestamp) {
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
    if (internal->opts.restoreall != 2)
      decide_scheduling (*p, timestamp);
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

// Compacting the witness_order stack
void External::compact_witness_order () {
  
  VERBOSE (3, "compacting witness order stack of size %zu", 
           witness_order.size ());

  auto begin = witness_order.begin ();
  auto end = witness_order.end ();
  auto q = begin;

  for (auto p = begin; p != end; ++p) {
    const int ewit = *p;
    const unsigned uwit = elit2ulit (ewit);
    // Keep the witness entries corresponding to clauses which were skipped
    // during restoration.
    if (u_marked (processed, uwit)) {
      assert (uwit < restore_start.size ());
      if (restore_start[uwit]) {
        restore_start[uwit]--;
        *q++ = ewit;
      }
      continue;
    }    

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

void External::restore_clauses (unsigned uwit, uint32_t ts, 
                                RestoreStats &clauses) {

  VERBOSE (3, "restoring clauses with stamp >= %u on witness stack %u (ulit) of size %zu ", ts, uwit, witness_stacks[uwit].size ());
  vector<int> &stack = witness_stacks[uwit];
  auto p = stack.begin ();
  auto end_of_stack = stack.end ();
  // 0 ts idu idl 0 l1 l2 ... lk next clause
  // ^
  LOG (stack, "witness_stack: ");
  uint32_t skipped = 0;
  while (p != end_of_stack) {
    assert (!*p); // p is on '0' 
    p++; // now on stamp. 
    // TODO: if stamp is zero we have a shared clause, now dereference pointer
    // else
    const uint32_t clause_stamp = static_cast<uint32_t> (*p);
    assert (clause_stamp);
    if (clause_stamp >= ts) {
      LOG ("Found first clause to be restored with time stamp %u", clause_stamp);
      --p;
      break;
    }
    skipped++;
    p += 3; // now on '0' after the id/pointer part
    // Skip to next clauses first '0' 
    while (++p != end_of_stack && *p)
      continue;
  }
  // p is on the '0' of the first clause to be restored
  auto cutoff = p;
  while (p != end_of_stack) {
    p++; // stamp
    const uint32_t clause_stamp = static_cast<uint32_t> (*p);
    assert (clause_stamp >= ts);
    p++; // idu
    clauses.weakened++;
    // copy the id of the clause
    const int64_t id = ((int64_t) (*p) << 32) + (int64_t) *(p + 1);
    int satisfied = 0;
    if (id) {
      LOG ("id is %" PRId64, id);
      p += 3; // idu -> idl -> 0 -> first literal

      auto begin = p;
      // now p is on the first literal of the clause. Check satisfied and
      // proceed pointer to the next clause (or end of stack)
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
          restore_clause (begin, p, id, clause_stamp);
      }
    }
  }
  clauses.seenbytes += sizeof (int) * stack.size ();
  // Now resize so that everything after cutoff (including cutoff is deleted)
  const size_t new_size = cutoff - stack.begin ();
  stack.resize (new_size);
  // Only if all clauses from this stack have been restored update witness
  if (stack.empty ())
    u_unmark (witness, uwit);
  u_mark (processed, uwit); 
  // We reuse restore_start[uwit] to store the number of retained clauses.
  // I.e. if processed[uwit] then the value of restore_start[uwit] is not a 
  // priority anymore. We need this value to realize compacting witness_order
  // correctly.
  set_restore_start (uwit, skipped); 
}

void External::propagate_tainting (RestoreStats &clauses) {
  while (!tainted_heap.empty ()) {
    const unsigned uwit = tainted_heap.pop_front ();
    const uint32_t ts = get_restore_start (uwit);
    assert (ts);

    LOG ("restoring clauses with witness %u (ulit) and time stamp >= %u", uwit, ts);
    restore_clauses (uwit, ts, clauses);
  }
}

void External::restore_all (RestoreStats &clauses) {
  assert (internal->opts.restoreall == 2);
  LOG ("restoring all clauses");
  for (unsigned uwit = 1; uwit < witness_stacks.size (); ++uwit) {
    if (witness_stacks[uwit].empty ())
      continue;
    restore_clauses (uwit, 0, clauses);
  }
  witness.clear (); // There should be no more clauses left on the stacks
  witness_order.clear ();
}

void External::restore () {
  START (restore);
  restoring = true;
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
  }
#endif

  if (internal->opts.restoreall == 2) {
    restore_all (clauses);
  } 
  else if (!tainted_lits.empty ()) {
    // TODO: Now initialize the heap from tainted_lits and clear the stack afterward
    for (auto elit : tainted_lits) {
      const unsigned uwit = elit2ulit (-elit);
      vector<int> &stack = witness_stacks[uwit];
      
      if (stack.empty ())
        continue;

      // TODO: check for zero time stamp (or zero id) and then 
      //       look up the time stamp in the shared clause instead.

      // Get time stamp of first clause on the corresp. witness stack
      // 0 ts idu idl 0 l1 l2 ...
      const uint32_t ts = static_cast<uint32_t> (stack[1]);
      // and schedule it. 
      assert (!get_restore_start (uwit));
      schedule (uwit, ts);
    }
    tainted_lits.clear ();

    for (const auto &s : witness_stacks)
      clauses.totalbytes += s.size () * sizeof (int);

    propagate_tainting (clauses);
    
    // "resize" witness vector  
    while (!witness.empty () && !witness.back ())
      witness.pop_back ();

    if (internal->opts.restorecompact) 
      compact_witness_order ();

    restore_start.clear();
    processed.clear ();
    assert (tainted_heap.empty ());

    internal->stats.restore_total_bytes += clauses.totalbytes;
    internal->stats.restore_seen_bytes += clauses.seenbytes;
    restoring = false;
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
} // namespace CaDiCaL
