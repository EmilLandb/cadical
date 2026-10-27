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

static void u_unmark (vector<bool> &map, unsigned ulit) {
  if (ulit < map.size ())
    map[ulit] = false;
}
/*------------------------------------------------------------------------*/ 
void External::restore_clause (const int* begin, const int* end,
                               const int64_t id,
                               const int ewit, const int blit) {
  LOG ("restoring clause...");
  LOG (begin, static_cast<unsigned> (end - begin), "restoring external clause[%" PRId64 "]", id);
  
  assert (eclause.empty ());
  assert (id);

  auto restore_lit = [this] (int elit) {
    eclause.push_back (elit);

    if (internal->proof && internal->lrat) {
      unsigned eidx = (elit > 0) + 2u * (unsigned) abs (elit);
      assert ((size_t) eidx < ext_units.size ());
      const int64_t unit_id = ext_units[eidx];
      bool added = ext_flags[abs (elit)];
      if (unit_id && !added) {
        ext_flags[abs (elit)] = true;
        internal->lrat_chain.push_back (unit_id);
      }
    }

    const int ilit = internalize (elit);
    internal->add_original_lit (ilit);
    internal->stats.restored_literals++;
  };

  for (auto p = begin; p != end; p++) {
    restore_lit (*p);
  }
  if (blit) {
    LOG ("adding blocking literal (external %d) back to the clause", blit);
    restore_lit (blit);
  }
  if (ewit) {
    LOG ("adding witness (external %d) back to the clause", ewit);
    restore_lit (ewit);
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


// NEW VERSION 
void External::restore_shared_stack (uint32_t ss_idx, RestoreStats &clauses) {

  WitnessStack &ss = shared_stacks[ss_idx];
  assert (!ss.empty ());
  LOG (ss.begin (), static_cast<unsigned> (ss.end () - ss.begin ()), "restoring shared stack: ");
  auto q = ss.begin ();
  auto end_of_stack = ss.end ();
  bool restore_clauses = false;
  // first skip the cube segment (0 terminated)
  while (*q) {
    const int ewit = *q++;
    if (marked (tainted, -ewit))
      restore_clauses = true;
  }
  while (*q) {
    q++;
  }
  q++;
  if (!restore_clauses && !(internal->opts.restoreall == 2)) {
    LOG ("untainted and not forced to restore all.");
    return;
  }
  // q now points to the first size field
  while (q != end_of_stack) {
    LOG ("encoded size field: %d", *q);
    bool wit_embedded, id_long; 
    unsigned other_lits_size;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);
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
      restore_clause (begin, end, id, 0, 0); 
    }
    // es (idu) idl l1 ... lk es es2
    q += 1 + (id_long ? 2 : 1) + other_lits_size + 1;
  }
  // Finally clear the data
  ss.clear (arena);
}


/* -------------------------------------------------------------------------- */


void External::restore_next (const int ewit, const int blit, RestoreStats &clauses) {
  const unsigned uwit = elit2ulit (ewit);
  WitnessStack &stack = witness_stacks[uwit];
  assert(ws_index[uwit] < stack.size() - 2);
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
    const uint64_t upper = static_cast<uint32_t> (*(p + 1));
    const uint64_t lower = static_cast<uint32_t> (*(p + 2));
    id = static_cast<int64_t> ((upper << 32) | lower);
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
    LOG (begin, static_cast<unsigned> (end_of_lits - begin), 
         "forced to not remove %d satisfied", satisfied);
    satisfied = 0;
  }

  if (satisfied) {
    clauses.satisfied++;
  } else {
    clauses.restored++;
    restore_clause (begin, end_of_lits, id, ewit, blit);
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

    
  ws_index.resize (witness_stacks.size ());
  restoring.resize (witness_stacks.size ());

  auto read = witness_order.begin ();
  auto write = witness_order.begin (); 
  auto end = witness_order.end ();

  while (read != end) {
    const int ewit = *read++;
    const int blit = *read++;
    if (!ewit) { // cube stack reference
      const uint32_t ss_idx = static_cast<uint32_t> (blit);
      restore_shared_stack (ss_idx, clauses);
      continue;
    }
    // restore the corresponding clause
    if (internal->opts.restoreall == 2 || marked (tainted, -ewit)) { 
      restore_next (ewit, blit, clauses);
      continue;
    }

    if (ewit) {
      const unsigned uwit = elit2ulit (ewit);
      // no clause on this stack should have been restored yet
      assert (!marked (restoring, ewit)); 
      ++ws_index[uwit]; // skip this clause   
    }
    *write++ = ewit;
    *write++ = blit;
  }
  witness_order.resize (write - witness_order.begin ());
  //shrink_vector (witness_order);

  for (const auto &cutoff : restore_cutoffs) {
    auto &stack = witness_stacks[cutoff.uwit];
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
  while (!witness_stacks.empty () && witness_stacks.back ().empty ())
    witness_stacks.pop_back ();
  witness_stacks.shrink_to_fit ();
  
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

} // namespace CaDiCaL
