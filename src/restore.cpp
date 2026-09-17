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

void External::set_priority (unsigned ulit, uint32_t timestamp) {
  if (priority.size () <= ulit)
    priority.resize (ulit + 1, 0);

  priority[ulit] = timestamp;
  LOG ("set priority of %u (unsigned) to %u", ulit, timestamp);
}

uint32_t External::get_priority (unsigned ulit) const {
  if (priority.size () <= ulit)
    return 0;
  return priority[ulit];
}

void External::decide_scheduling (int elit, uint32_t clause_ts) {
  const unsigned uwit = elit2ulit (-elit); // wit. that could need restoration
  LOG ("deciding scheduling for %d (unsigned %u) with time stamp %u", elit, uwit, clause_ts);

  if (!u_marked (witness, uwit)) // No clause with corresp. witness
    return;
  if (get_priority (uwit)) // is already scheduled correctly
    return;

  // uwit has never been scheduled and we need to find the actual time stamp at
  // which we need to restore it
  vector<int> &stack = witness_stacks[uwit];
  uint32_t idx = 0;
  uint32_t event_ts;
  while (idx < stack.size ()) {
    assert (!stack[idx]);

    event_ts = timestamp (stack, idx);
    LOG ("event timestamp is %u", event_ts);

    if (event_ts >= clause_ts)
      break;
    idx = next_event (stack, idx);
  }

  // set priority correctly and push to the heap
  if (idx == stack.size ())
    return;

  ws_index[uwit] = idx; //todo make this external scope
  set_priority (uwit, event_ts);
  tainted_heap.push (uwit);
  restore_cutoffs.push_back ({uwit, idx});
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

void External::restore_shared_stack (SharedStack *ss, RestoreStats &clauses) {
  const uint32_t shared_stamp = ss->stamp;
  VERBOSE (3, "restoring clauses with stamp %u on shared stack of size %zu ", 
           shared_stamp, ss->clause_data.size ());
  LOG (ss->clause_data, "shared stack clauses: ");
  LOG (ss->witness_cube, "shared stack cube: ");
  // The entries on clause_data look as follows:
  // 0 id_u id_l 0 l1 l2 ... lk 0 id_u id_l 0 l1 ...
  vector<int> &stack = ss->clause_data;
  auto p = stack.begin ();
  auto end_of_stack = stack.end ();
  while (p != end_of_stack) {
    p++; // idu
    clauses.weakened++;
    // copy the id of the clause
    const int64_t id = ((int64_t) (*p) << 32) + (int64_t) *(p + 1);
    int satisfied = 0;
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
             "flushing implied %s clause satisfied by %d from shared stack", 
             id ? "" : "dummy", satisfied);
        clauses.satisfied++;
    } else {
      clauses.restored++;
      if (id)
        restore_clause (begin, p, id, shared_stamp);
    }
  }     
  clauses.seenbytes += sizeof (int) * stack.size ();
  clauses.totalbytes += sizeof (int) * stack.size (); // TODO: This is not really doing that

  // Clear the shared stack but only free if this is the last existing reference
  stack.clear ();
  ss->witness_cube.clear ();
  assert (ss->backlinks);
  ss->backlinks--;
  if (!ss->backlinks)
    delete ss;
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
    const uint32_t clause_stamp = static_cast<uint32_t> (*p);
    if (!clause_stamp) { // shared stack case
      // 0 0 0 pu pl 0
      //   ^
      const uintptr_t ptr =
          (static_cast<uintptr_t> (static_cast<uint32_t> (*(p + 2))) << 32) |
           static_cast<uint32_t> (*(p + 3));
      SharedStack *ss = reinterpret_cast<SharedStack*> (ptr);
      const uint32_t shared_stamp = ss->stamp;
      if (shared_stamp >= ts) {
        LOG ("Found first reconstruction entry to be restored with time stamp %u", shared_stamp);
        --p;
        break;
      }
      // progress to next clauses first '0' or end of stack
      p += 4;
    } 
    else { // regular clause
      if (clause_stamp >= ts) {
        LOG ("Found first reconstruction entry to be restored with time stamp %u", clause_stamp);
        --p;
        break;
      }  
      p += 3; // now on '0' before literals or on p_l
      // Skip to next clauses first '0' 
      while (++p != end_of_stack && *p)
        continue;
      // Only update skipped for regular clauses! 
      // Shared clauses are not associated with uwit on witness_order
      skipped++; 
    }
  }
  // p is on the '0' of the first clause to be restored
  auto cutoff = p;
  while (p != end_of_stack) {
    p++; // stamp
    const uint32_t clause_stamp = static_cast<uint32_t> (*p);
    if (!clause_stamp) { // Shared Stack!
      // 0 0 0 pu pl 0
      //   ^
      const uintptr_t ptr =
          (static_cast<uintptr_t> (static_cast<uint32_t> (*(p + 2))) << 32) |
           static_cast<uint32_t> (*(p + 3));
      SharedStack *ss = reinterpret_cast<SharedStack*> (ptr);
      assert (ss->stamp >= ts);
      restore_shared_stack (ss, clauses);
      p += 4;
    } 
    else { // Regular clause
      assert (clause_stamp >= ts);
      p++; // idu
      clauses.weakened++;
      // copy the id of the clause
      const int64_t id = ((int64_t) (*p) << 32) + (int64_t) *(p + 1);
      int satisfied = 0;
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
  //u_mark (processed, uwit); 
  // We reuse priority[uwit] to store the number of retained clauses.
  // I.e. if processed[uwit] then the value of priority[uwit] is not a 
  // priority anymore. We need this value to realize compacting witness_order
  // correctly.
  set_priority (uwit, skipped); 
}

/* -------------------------------------------------------------------------- */
// Get the time stamp of the clause at idx on stack
uint32_t External::timestamp (const vector<int> &stack, uint32_t idx) {
  assert (idx < stack.size ());
  assert (!stack[idx]);
  const uint32_t ts = static_cast<uint32_t> (stack[idx + 1]);
  if (ts)
    return ts;
  // Shared stack: 0 0 0 pu pl
  const uintptr_t ptr = (static_cast<uintptr_t> (
                            static_cast<uint32_t> (stack[idx + 3])) << 32) |
                            static_cast<uint32_t> (stack[idx + 4]);
  SharedStack *ss = reinterpret_cast<SharedStack *> (ptr);
  return ss->stamp;                         
}

// Returns the index of the next restoration event (next clause or next shared stack reference)
uint32_t External::next_event (const vector<int> &stack, uint32_t idx) {
  assert (idx < stack.size ());
  assert (!stack[idx]);

  if (stack[idx + 1]) { // Regular clause 0 ts idu idl 0 l1 ... lk
    idx += 5; // first literal
    while (idx < stack.size () && stack[idx])
      ++idx;
    return idx;
  }

  // Shared stack reference: 0 0 0 ptr_u ptr_l
  return idx + 5;
}

uint32_t External::restore_event (vector<int> &stack, uint32_t idx, RestoreStats &clauses) {
  assert (idx < stack.size ());
  assert (!stack[idx]);

  const uint32_t clause_stamp = timestamp (stack, idx);

  if (!stack[idx + 1]) { // Shared stack: 0 0 0 pu pl
    const uintptr_t ptr = (static_cast<uintptr_t> (
                           static_cast<uint32_t> (stack[idx + 3])) << 32) |
                           static_cast<uint32_t> (stack[idx + 4]);

    SharedStack *ss = reinterpret_cast<SharedStack *> (ptr);

    restore_shared_stack (ss, clauses);

    return idx + 5;
  }

  // Regular clause: 0 ts idu idl 0 l1 l2 ... lk
  const int64_t id =
      (static_cast<int64_t> (stack[idx + 2]) << 32) |
       static_cast<uint32_t> (stack[idx + 3]);

  auto p = stack.begin () + idx + 5; // first literal
  auto end = stack.end ();
  auto begin = p;

  int satisfied = 0;

  while (p != end && *p) {
    if (!satisfied && fixed (*p) > 0)
      satisfied = *p;
    ++p;
  }
 
  if (satisfied && !internal->opts.restoreflush) {
    LOG (begin, p, "forced to not remove %d satisfied", satisfied);
    satisfied = 0;
  }

  if (satisfied) {
    clauses.satisfied++;
  } else {
    clauses.restored++;
    restore_clause (begin, p, id, clause_stamp);
  }

  return p - stack.begin ();
}
/* -------------------------------------------------------------------------- */
void External::restore_next (RestoreStats &clauses) {
  const unsigned uwit = tainted_heap.top ();
  tainted_heap.pop ();
  vector<int> &stack = witness_stacks[uwit];

  uint32_t idx = ws_index[uwit];
  
  assert (idx < stack.size ());
  assert (!stack[idx]);
  assert (timestamp (stack, idx) == get_priority (uwit));

  // restore clause starting at idx and continue to do so while the following
  // clause still has the highest priority
  while (true) {
    const uint32_t ts = timestamp (stack, idx);

    idx = restore_event (stack, idx, clauses);
    ws_index[uwit] = idx;

    if (idx == stack.size ())
      break;

    const uint32_t next_ts = timestamp (stack, idx);

    if (!tainted_heap.empty () && 
        next_ts >= get_priority (tainted_heap.top ()))
      break;
  }

  if (idx != stack.size ()) {
    const uint32_t next_ts = timestamp (stack, idx);
    set_priority (uwit, next_ts);
    tainted_heap.push (uwit);
  }
}

void External::propagate_tainting (RestoreStats &clauses) {

  while (!tainted_heap.empty ()) {
    const unsigned uwit = tainted_heap.top ();
    const uint32_t ts = get_priority (uwit);
    assert (ts);

    //restore_clauses (uwit, ts, clauses);
    restore_next (clauses);
  }

  for (const auto &cutoff : restore_cutoffs)
    witness_stacks[cutoff.uwit].resize (cutoff.idx);
}

void External::restore_all (RestoreStats &clauses) {
  assert (internal->opts.restoreall == 2);
  LOG ("restoring all clauses");
  for (unsigned uwit = 0; uwit < witness_stacks.size (); ++uwit) {
    if (witness_stacks[uwit].empty ())
      continue;
    restore_clauses (uwit, 0, clauses);
  }
  witness.clear (); // There should be no more clauses left on the stacks
}

void External::restore () {
  PROFILE_SCOPE (restore);
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
    assert (ws_index.empty ());
    assert (restore_cutoffs.empty ());
    ws_index.resize (witness_stacks.size ());
    for (auto elit : tainted_lits) {
      const unsigned uwit = elit2ulit (-elit);
      LOG ("tainted literal %d (external) (%u unsigned)", elit, uwit);
      vector<int> &stack = witness_stacks[uwit];
      LOG (stack, "witness_stack[%u]: ", uwit);
      if (stack.empty ()) // TODO: That should not be possible
        continue;

      auto p = stack.begin ();
      // Get time stamp of first clause on the corresp. witness stack
      // 0 ts idu idl 0 l1 l2 ...
      while (p != stack.end ()) {
        assert (!*p);

        if (*(p + 1)) { // regular clause
          break;
        }
        LOG ("shared clause detected.");
        // Shared stack: 0 0 0 pu pl 0
        const uintptr_t ptr =
            (static_cast<uintptr_t> (static_cast<uint32_t> (*(p + 3))) << 32) |
                                     static_cast<uint32_t> (*(p + 4));

        SharedStack *ss = reinterpret_cast<SharedStack *> (ptr);
        
        if (!ss->witness_cube.empty ())
          break;
        // TODO: can this happen? 
        // Stale shared stack. Just skip over its witness-stack representation.
        p += 5;
      }
      // Schedule with priority ts
      if (p != stack.end ()) {
        const uint32_t idx = p - stack.begin ();
        const uint32_t ts = timestamp (stack, idx);
        LOG ("restoration event to be scheduled begins at idx %u with time stamp %u", idx, ts);
        assert (ts);
        assert (!get_priority (uwit));
        ws_index[uwit] = idx;
        
        set_priority (uwit, ts);
        tainted_heap.push (uwit);
        restore_cutoffs.push_back ({uwit, idx});
        LOG ("pushed to heap...");
      }      
    }
    tainted_lits.clear ();

    // TODO: this does not account for shared stack sizes...
    for (const auto &s : witness_stacks)
      clauses.totalbytes += s.size () * sizeof (int);

    propagate_tainting (clauses);
    
    // "resize" witness vector  
    while (!witness.empty () && !witness.back ())
      witness.pop_back ();

    priority.clear ();
    ws_index.clear ();
    restore_cutoffs.clear ();
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
}

} // namespace CaDiCaL
