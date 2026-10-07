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
static constexpr uint32_t CLAUSE_SMALL = 1u << 31;
static constexpr uint32_t EMBEDDED     = 1u << 30;
static constexpr uint32_t ID_LONG     = 1u << 29;
static constexpr uint32_t SIZE_MASK   = (1u << 29) - 1;
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
void External::restore_clause (const int* begin,
                               const int* end,
                               const int64_t id, const bool wit_embedded,
                               const int ewit) {
  LOG (begin, static_cast<unsigned> (end - begin), "restoring external clause[%" PRId64 "]", id);
  
  assert (eclause.empty ());
  assert (id);
  assert (!wit_embedded || ewit);
  if (wit_embedded) {
    LOG ("adding witness (external %d) back to the clause", ewit);
    eclause.push_back (ewit);
    if (internal->proof && internal->lrat) {
      unsigned eidx = (ewit > 0) + 2u * (unsigned) abs (ewit);
      assert ((size_t) eidx < ext_units.size ());
      const int64_t id = ext_units[eidx];
      bool added = ext_flags[abs (ewit)];
      if (id && !added) {
        ext_flags[abs (ewit)] = true;
        internal->lrat_chain.push_back (id);
      }  
    }
    int ilit = internalize (ewit);
    internal->add_original_lit (ilit), internal->stats.restored_literals++;
  }

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
/*
void External::restore_clause (const vector<int>::const_iterator &begin,
                               const vector<int>::const_iterator &end,
                               const int64_t id, const bool wit_embedded,
                               const int ewit) {
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
*/
/* -------------------------------------------------------------------------- */
inline void decode_size_field (const int size_field, bool &wit_embedded, 
                               bool &id_long, unsigned &other_lits_size) {
  assert (size_field);

  const uint32_t encoded = static_cast<uint32_t> (size_field);
  const bool clause_small = encoded & CLAUSE_SMALL;

  wit_embedded = clause_small && (encoded & EMBEDDED);
  id_long = !clause_small || (encoded & ID_LONG);
  other_lits_size = clause_small ? (encoded & SIZE_MASK) : encoded;
}

/*
// NEW VERSION 
void External::restore_shared_stack_c (int *p, RestoreStats &clauses) {
  assert (!*p);
  const uint32_t ss_idx = static_cast<uint32_t> (*(p + 1));
  SharedStack &ss = shared_stacks[ss_idx];
  assert (!ss.empty ());
  assert (ss.backlinks);

  auto q = ss.begin ();
  auto end_of_stack = ss.end ();
  // first skip the cube segment (0 terminated)
  while (*q++) 
    continue;
  // q now points to the first size field
  while (q != end_of_stack) {
    bool wit_embedded, id_long; 
    unsigned other_lits_size;
    decode_size_field (p, wit_embedded, id_long, other_lits_size);
    assert (!wit_embedded);
    
    int64_t id;
    if (id_long) {
      id = (static_cast<int64_t> (*(q + 1)) << 32) |
          static_cast<uint32_t> (*(q + 2));
    } else {
      id = static_cast<uint32_t> (*(q + 1));
    }

    LOG ("id computed: %" PRId64 "(%s)", id, id_long ? "long" : "short");
    auto lit = q + (id_long ? 3 : 2); // es (idu) idl l1 
    auto begin = lit;
    auto end = lit + other_lits_size;
    int satisfied = 0;
    while (lit != end) {
      if (!satisfied && fixed (*lit) > 0)
        satisfied = *lit;
      ++lit;
    }
    if (satisfied && !internal->opts.restoreflush) {
      LOG (begin, static_cast<unsigned> (end - begin), 
        "forced to not remove %d satisfied", satisfied);
      satisfied = 0;
    }
    if (satisfied) {
      clauses.satisfied++;
    } else {
      clauses.restored++;
      restore_clause_c (begin, end, id, ss.stamp, wit_embedded, 0);
    }
    // es (idu) idl l1 ... lk es es2
    q += 1 + (id_long ? 2 : 1) + other_lits_size + 1;
  }
  // Finally clear the data
  ss.data.clear (arena);
}
*/

/* -------------------------------------------------------------------------- */


void External::restore_next (const int ewit, RestoreStats &clauses) {
  const unsigned uwit = elit2ulit (ewit);
  assert(ws_index[uwit] < stack.size() - 2);
  WitnessStack &stack = witness_stacks2[uwit];
  bool wit_embedded, id_long;
  unsigned other_lits_size;

  if (!marked (restoring, ewit)) { // This is the first clause to be restored
    uint32_t skipped = ws_index[uwit]; // Skip this many entries
    uint32_t idx = 0;
    while (skipped--) {
      const int size_field = stack[idx];
    
      decode_size_field (size_field, wit_embedded, id_long, other_lits_size);

      // Skip the clause and move idx to the next clauses size field                 
      idx += (id_long ? 3 : 2) + other_lits_size + 1;
    }
    ws_index[uwit] = idx;
    restore_cutoffs.push_back ({uwit, idx});
    mark (restoring, ewit);
  }
  // Now restore the next clause ...
  auto p = stack.begin () + ws_index[uwit];
  decode_size_field (*p, wit_embedded, id_long, other_lits_size);

  int64_t id;
  if (id_long) {
    id = (static_cast<int64_t> (*(p + 1)) << 32) |
          static_cast<uint32_t> (*(p + 2));
  } else {
    id = static_cast<uint32_t> (*(p + 1));
  }
  LOG ("id computed: %" PRId64 "(%s)", id, id_long ? "long" : "short");
  
  auto lit = p + (id_long ? 3 : 2); // idx is of the first literal now
  auto begin = lit;
  auto end_of_lits = lit + other_lits_size;

  int satisfied = 0;
  while (lit != end_of_lits) {
    if (!satisfied && fixed (*lit) > 0)
      satisfied = *lit;
    ++lit;
  }

  if (!satisfied && wit_embedded) {
    if (fixed (ewit) > 0)
      satisfied = ewit;
  }

  if (satisfied && !internal->opts.restoreflush) {
    LOG (begin, static_cast<unsigned> (end - begin), 
         "forced to not remove %d satisfied", satisfied);
    satisfied = 0;
  }

  if (satisfied) {
    clauses.satisfied++;
  } else {
    clauses.restored++;
    restore_clause (begin, end_of_lits, id, wit_embedded, ewit);
  }
  // idx now points to next clauses first size field
  const uint32_t idx = end_of_lits + 1 - stack.begin (); 
  ws_index[uwit] = idx;
} 

// NEW VERSION // _c
void External::restore () {
  PROFILE_SCOPE (restore);
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
// --------------------------------------------------------
  if (tainted.empty () && internal->opts.restoreall != 2)
    return;
  
  assert (ws_index.empty ());
  assert (restore_cutoffs.empty ());

    
  ws_index.resize (witness_stacks2.size ());
  restoring.resize (witness_stacks2.size ());

  auto read = witness_order.begin ();
  auto write = witness_order.begin (); 
  auto end = witness_order.end ();

  while (read != end) {
    const int ewit = *read++;

    // restore the corresponding clause!
    if (internal->opts.restoreall == 2 || marked (tainted, -ewit)) { 
      restore_next (ewit, clauses);
      continue;
    }

    const unsigned uwit = elit2ulit (ewit);
    // no clause on this stack should have been restored yet
    assert (!marked (restoring, ewit)); 
    ++ws_index[uwit]; // skip this clause 
    *write++ = ewit;
  }
  witness_order.resize (write - witness_order.begin ());
  witness_order.shrink_to_fit ();

  for (const auto &cutoff : restore_cutoffs) {
    auto &stack = witness_stacks2[cutoff.uwit];
    stack.truncate (cutoff.idx + 2, arena); // add two for the size and capacity fields
    stack.shrink_to_fit (arena);
    if (stack.empty ()) {
      u_unmark (witness, cutoff.uwit);
    }
  }

  // "resize" witness vector  
  while (!witness.empty () && !witness.back ())
    witness.pop_back ();
  
  // 'resize' witness stacks
  while (!witness_stacks2.empty () && witness_stacks2.back ().empty ())
    witness_stacks2.pop_back ();
  witness_stacks2.shrink_to_fit ();
  
  ws_index.clear ();
  ws_index.shrink_to_fit ();
  restore_cutoffs.clear ();
  restore_cutoffs.shrink_to_fit ();
  restoring.clear ();
  restoring.shrink_to_fit ();

  internal->stats.restore_total_bytes += clauses.totalbytes;
  internal->stats.restore_seen_bytes += clauses.seenbytes;

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
  tainted.shrink_to_fit ();
} 

/*
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
  { // TODO: remove this again after evaluation
    internal->stats.restore_ws_size += witness_stacks.size ();
    for (const auto &stack : witness_stacks)
      if (stack.size ()) {
        internal->stats.restore_nstacks++;
        internal->stats.restore_nints += stack.size ();
        internal->stats.restore_caps += stack.capacity ();
      }
  }
#endif

  if (internal->opts.restoreall == 2) {
    restore_all (clauses);
  } 
  else if (!tainted_lits.empty ()) {
    assert (ws_index.empty ());
    assert (restore_cutoffs.empty ());
    assert (priority.empty ());
    ws_index.resize (witness_stacks.size ());
    for (auto elit : tainted_lits) {
      const unsigned uwit = elit2ulit (-elit);
      LOG ("tainted literal %d (external) (%u unsigned)", elit, uwit);
      //if (uwit >= witness_stacks.size ())
      //  continue;
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
    tainted_lits.shrink_to_fit ();

    // TODO: this does not account for shared stack sizes...
    for (const auto &s : witness_stacks)
      clauses.totalbytes += s.size () * sizeof (int);

    propagate_tainting (clauses);
    
    // "resize" witness vector  
    while (!witness.empty () && !witness.back ())
      witness.pop_back ();
    
    // 'resize' witness stacks
    while (!witness_stacks.empty () && witness_stacks.back ().empty ())
      witness_stacks.pop_back ();
    witness_stacks.shrink_to_fit ();
    
    ws_index.clear ();
    ws_index.shrink_to_fit ();
    restore_cutoffs.clear ();
    restore_cutoffs.shrink_to_fit ();

    assert (tainted_heap.empty ());    
    //tainted_heap = RestoreHeap(PriorityLess(priority));

    internal->stats.restore_total_bytes += clauses.totalbytes;
    internal->stats.restore_seen_bytes += clauses.seenbytes;
    restoring = false;
  }

  priority.clear();
  priority.shrink_to_fit ();

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
  tainted.shrink_to_fit ();
} 
*/
} // namespace CaDiCaL
