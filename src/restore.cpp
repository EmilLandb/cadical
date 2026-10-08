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

// NEW VERSION
void External::decide_scheduling_c (int elit, uint32_t clause_ts) {
  const unsigned uwit = elit2ulit (-elit); // wit. that could need restoration
  LOG ("deciding scheduling for %d (unsigned %u) with time stamp %u", elit, uwit, clause_ts);

  if (!u_marked (witness, uwit)) // No clause with corresp. witness
    return;
  if (get_priority (uwit)) // is already scheduled
    return;

  // uwit has never been scheduled and we need to find the actual time stamp at
  // which we need to restore it
  WitnessStack &stack = witness_stacks2[uwit];
  auto p = stack.begin ();
  uint32_t event_ts;
  LOG (stack.begin (), (stack.end () - stack.begin ()), "stack: ");
  while (p != stack.end ()) {
    LOG ("p value: %d", *p);
    event_ts = timestamp_c (p);
    LOG ("event timestamp is %u", event_ts);

    if (event_ts >= clause_ts)
      break;

    p = next_event_c (p);
  }
  
  if (p == stack.end ())
    return;

  const uint32_t idx = p - stack.begin ();
  ws_index[uwit] = idx;
  set_priority (uwit, event_ts);
  tainted_heap.push (uwit);
  restore_cutoffs.push_back ({uwit, idx});
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

// NEW VERSION
void External::restore_clause_c (const int *begin, const int* end, 
                                 const int64_t id, const uint32_t timestamp, 
                                 const bool wit_embedded, const int ewit) {
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
    if (internal->opts.restoreall != 2)
      decide_scheduling_c (ewit, timestamp);
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
    if (internal->opts.restoreall != 2)
      decide_scheduling_c (*p, timestamp);
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
      //restore_shared_stack (ss, clauses);
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
// NEW VERSION. p points to the first size field of the clause
uint32_t External::timestamp_c (int *p) {
  if (*p) {
    const uint32_t ts = static_cast<uint32_t> (*(p + 1));
    assert (ts);
    return ts;
  }
  // shared stack reference
  const uint32_t ss_idx = static_cast<uint32_t> (*(p + 1));
  SharedStack &ss = shared_stacks[ss_idx];
  return ss.stamp;
}

inline void decode_size_field (const int *size_field, bool &wit_embedded, 
                               bool &id_long, unsigned &other_lits_size) {
  assert (*size_field);

  const uint32_t encoded = static_cast<uint32_t> (*size_field);
  const bool clause_small = encoded & CLAUSE_SMALL;

  wit_embedded = clause_small && (encoded & EMBEDDED);
  id_long = !clause_small || (encoded & ID_LONG);
  other_lits_size = clause_small ? (encoded & SIZE_MASK) : encoded;
}

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

// NEW VERSION
int* External::next_event_c (int* p) {
  if (!*p)
    return p + 2;

  bool wit_embedded, id_long; 
  unsigned other_lits_size;
  decode_size_field (p, wit_embedded, id_long, other_lits_size);
  // es ts (idu) idl l1 ... lk es es2 ts2 ...
  return p + 1 + (id_long ? 2 : 1) + other_lits_size + 2;
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

// NEW VERSION
int* External::restore_event_c (int *p, unsigned uwit, RestoreStats &clauses) {
  // TODO: shared stack case 
  if (!*p) {
    const uint32_t ss_idx = static_cast<uint32_t> (*(p + 1));
    SharedStack &ss = shared_stacks[ss_idx];
    
    if (!ss.empty ())
      restore_shared_stack_c (p, clauses);
    assert (ss.empty ());
    assert (ss.backlinks);
    if (!--ss.backlinks)
      shared_stacks.deallocate (ss_idx);

    return p + 2;
  }
  bool wit_embedded, id_long; 
  unsigned other_lits_size;
  decode_size_field (p, wit_embedded, id_long, other_lits_size);
  //  v +1  +2   +3  +4 
  // es ts [idu] idl l1 .. lk es
  int64_t id;
  if (id_long) {
    id = (static_cast<int64_t> (*(p + 2)) << 32) |
          static_cast<uint32_t> (*(p + 3));
  } else {
    id = static_cast<uint32_t> (*(p + 2));
  }
  LOG ("id computed: %" PRId64 "(%s)", id, id_long ? "long" : "short");
  auto lit = p + (id_long ? 4 : 3);
  auto begin = lit;
  auto end = lit + other_lits_size;
  int satisfied = 0;
  while (lit != end) {
    if (!satisfied && fixed (*lit) > 0)
      satisfied = *lit;
    ++lit;
  }
  if (!satisfied && wit_embedded) {
    const int sign = static_cast<int> (uwit & 1);
    const int ewit = ((static_cast<int> (uwit >> 1) + 1 ^ -sign) + sign);
    if (fixed (ewit) > 0)
      satisfied = ewit;
  }
  
  if (satisfied && !internal->opts.restoreflush) {
    LOG (begin, static_cast<unsigned> (end - begin), "forced to not remove %d satisfied", satisfied);
    satisfied = 0;
  }

  if (satisfied) {
    clauses.satisfied++;
  } else {
    clauses.restored++;
    const int sign = static_cast<int> (uwit & 1);
    const int ewit = ((static_cast<int> (uwit >> 1) + 1 ^ -sign) + sign);
    LOG ("ewit computed: %d (uwit: %u)", ewit, uwit);
    const uint32_t clause_stamp = timestamp_c (p);
    restore_clause_c (begin, end, id, clause_stamp, wit_embedded, ewit);
  }
  return end + 1; // Trailing size field
}

/* -------------------------------------------------------------------------- */
// NEW VERSION
void External::restore_next_c (RestoreStats &clauses) {
  const unsigned uwit = tainted_heap.top ();
  tainted_heap.pop ();
  WitnessStack &stack = witness_stacks2[uwit];
  const unsigned stack_size = stack.size () - 2;

  uint32_t idx = ws_index[uwit];
  auto p = stack.begin () + idx;
  assert (idx < stack_size);
  assert (timestamp_c (p) == get_priority (uwit));

  while (true) {
    p = restore_event_c (p, uwit, clauses);
    ws_index[uwit] = p - stack.begin ();
    if (p == stack.end ())
      break;

    const uint32_t next_ts = timestamp_c (p);
    if (!tainted_heap.empty () && next_ts >= get_priority (tainted_heap.top ()))
      break;
  }

  if (p != stack.end ()) {
    const uint32_t next_ts = timestamp_c (p);
    set_priority (uwit, next_ts);
    tainted_heap.push (uwit);
  }
}

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

    //idx = restore_event (stack, idx, clauses);
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

// NEW VERSION
void External::propagate_tainting_c (RestoreStats &clauses) {
  size_t tainted_heap_max_size = tainted_heap.size ();

  while (!tainted_heap.empty ()) {
    if (tainted_heap.size () > tainted_heap_max_size) // TODO: remove stat
      tainted_heap_max_size = tainted_heap.size ();
    restore_next_c (clauses);
  }

  //printf ("tainted_heap_max_size: %zu (bytes)\n", tainted_heap_max_size * sizeof (int));
  //printf ("restore_cutoffs size: %zu (bytes)\n", restore_cutoffs.size () * sizeof (RestoreCutoff));
  size_t emptied_stacks = 0;
  for (const auto &cutoff : restore_cutoffs) {
    auto &stack = witness_stacks2[cutoff.uwit];
    stack.truncate (cutoff.idx + 2, arena); // add two for the size and capacity fields
    stack.shrink_to_fit (arena);
    if (stack.empty ()) {
      emptied_stacks++; // TODO: remove
      u_unmark (witness, cutoff.uwit);
    }
  }
  //printf ("emptied stacks: %zu\n", emptied_stacks);
}

void External::propagate_tainting (RestoreStats &clauses) {
  
  while (!tainted_heap.empty ()) {
    
    const unsigned uwit = tainted_heap.top ();
    const uint32_t ts = get_priority (uwit);
    assert (ts);

    //restore_clauses (uwit, ts, clauses);
    restore_next (clauses);
  }
  for (const auto &cutoff : restore_cutoffs) {
    auto &stack = witness_stacks[cutoff.uwit];
    stack.resize (cutoff.idx);
    
    if (stack.empty ())
      u_unmark (witness, cutoff.uwit);
  }
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

// NEW VERSION // _c
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
    internal->stats.restore_ws_size += witness_stacks2.size ();
    size_t nstacks = 0;
    size_t nints = 0;
    size_t caps = 0;
    std::vector<uint64_t> witness_stack_sizes;

    for (const auto &stack : witness_stacks2) {
        nstacks += !stack.empty ();
        nints += stack.size ();
        caps += stack.capacity ();
        if (!stack.empty ()) {
          const unsigned size = stack.size ();
          if (witness_stack_sizes.size () <= size)
            witness_stack_sizes.resize (size + 1, 0);
          ++witness_stack_sizes[size];
        }      
    }

    internal->stats.restore_nstacks += nstacks;
    internal->stats.restore_nints += nints;
    internal->stats.restore_caps += caps;
    printf ("witness stacks nonempty: %zu\n", nstacks);
    printf ("witness stacks sizes (bytes): %zu\n", nints * sizeof (int));
    printf ("witness stacks caps (bytes): %zu\n", caps * sizeof (int));
    printf ("witness arena stats:\n");
    printf ("reserved bytes: %llu\n", arena.reserved_bytes ());
    printf ("peak reserved bytes: %llu\n", arena.stats.peak_reserved_bytes);
    printf ("large allocations: %llu\n", arena.stats.large_allocations);
    printf ("large deallocations: %llu\n", arena.stats.large_deallocations);
    printf ("shrink count: %llu\n", arena.stats.shrink_count);
    printf ("shrink bytes saved: %llu\n", arena.stats.shrink_bytes_saved);
    for (unsigned i = 0; i < WitnessArena::NUM_CLASSES; ++i) {
      const auto &s = arena.stats;
      printf ("class %u\n", i);
      printf ("\tallocations: %llu\n", s.allocations[i]);
      printf ("\tdeallocations: %llu\n", s.deallocations[i]);
      printf ("\tchunks: %llu\n", s.chunks[i]);
      printf ("\tlive: %llu\n", s.live[i]);
      printf ("\tpeak_live: %llu\n", s.peak_live[i]);
      printf ("\tgrowths: %llu\n", s.growths[i]);
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
    ws_index.resize (witness_stacks2.size ());
    {
    //printf ("ws_index cap: %zu (bytes)\n", ws_index.capacity () * sizeof (int32_t));
    //printf ("priority cap: %zu (bytes)\n", priority.capacity () * sizeof (int32_t));
    //printf ("witness_stacks2 cap: %zu (bytes)\n", witness_stacks2.capacity () * sizeof (WitnessStack));
    //printf ("witness cap: %zu (bytes)\n", witness.capacity () * sizeof (bool));
    //printf ("tainted cap: %zu (bytes)\n", tainted.capacity () * sizeof (bool));  
    }
    for (auto elit : tainted_lits) {
      const unsigned uwit = elit2ulit (-elit);
      LOG ("tainted literal %d (external) (%u unsigned)", elit, uwit);
      WitnessStack &stack = witness_stacks2[uwit];
      LOG (stack.begin (), static_cast<unsigned> (stack.end () - stack.begin ()), "witness_stack[%u]: ", uwit);
      if (stack.empty ()) // TODO: That should not be possible. Depends on tainting condition...
        continue;

      auto p = stack.begin ();
      // Get time stamp of first clause on the corresp. witness stack:
      // enc_size ts (idu) idl l1 ... lk enc_size
      // or for a shared stack reference
      // 0 ss_idx 
      while (p != stack.end ()) {
        if (*p) { // regular clause
          break;
        } 
        // shared stack reference!
        assert (p + 1 < stack.end ());
        const uint32_t ss_idx = static_cast<uint32_t> (*(p + 1));
        SharedStack &ss = shared_stacks[ss_idx];
        if (!ss.empty ()) // invariant: a stale shared stack has its data cleared.
          break;
        assert (ss.backlinks);
        if (!--ss.backlinks) // Last reference will be removed -> free the block
          shared_stacks.deallocate (ss_idx);
        p += 2; // skip over stale shared stack  
      }
      // Schedule with priority ts
      if (p != stack.end ()) {
        const uint32_t idx = p - stack.begin ();
        const uint32_t ts = timestamp_c (p);
        LOG ("restoration event to be scheduled begins at idx %u with time stamp %u", idx, ts);
        assert (ts);
        assert (!get_priority (uwit));
        ws_index[uwit] = idx;
        
        set_priority (uwit, ts);
        tainted_heap.push (uwit);
        restore_cutoffs.push_back ({uwit, 0});
        LOG ("pushed to heap...");
      }      
    }
    tainted_lits.clear ();
    tainted_lits.shrink_to_fit ();

    // TODO: this does not account for shared stack sizes...
    for (const auto &s : witness_stacks2)
      clauses.totalbytes += s.size () * sizeof (int);

    propagate_tainting_c (clauses);
    
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
  //priority.shrink_to_fit (); // TODO: comment back in if this really does something

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

} // namespace CaDiCaL