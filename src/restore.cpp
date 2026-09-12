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

bool External::restore_shared_stack (vector<int> *ss, RestoreStats &clauses) {
  // w1 w2 ... wk C1 C2 ... Cm (clauses are represented as usual)
  auto p = ss->begin ();
  bool restore_ss = false;
  while (*p) {
    const int ewit = *p;
    if (marked (tainted, -ewit))
      restore_ss = true;
    ++p;
  }
  if (internal->opts.restoreall == 2)
    restore_ss = true;
  if (!restore_ss) {
    auto q = ss->begin ();
    while (*q) {
      const int ewit = *q;
      mark (remaining, ewit);
      ++q;
    }
    return false;
  }

  // restore all clauses in order
  auto end = ss->end ();
  while (p != end) {
    // p is on first '0' of next clause to be restored
    const int64_t upper = *++p;
    const int64_t lower = *++p;
    const int64_t id = (upper << 32) + lower;
    ++p;
    // p is on the '0' before the literals
    auto begin = ++p;
    int satisfied = 0;
    while (p != end && *p) {
      const int elit = *p;
      if (!satisfied && fixed (elit) > 0)
        satisfied = elit;
      ++p;
    }
    if (satisfied && !internal->opts.restoreflush) {
      LOG (begin, p, "forced to not remove %d satisfied", satisfied);
      satisfied = 0;
    }
    if (satisfied) {
      LOG (begin, p, 
          "flushing implied clause satisfied by %d from extension stack", 
          satisfied);
      clauses.satisfied++;
    } else {
        clauses.restored++;
        restore_clause (begin, p, id);
    }
  } 
  delete ss;
  return true;
}

void External::restore_in_order (RestoreStats &clauses) {
  // Maintaining indices into the witness stacks. Lazily updated using skipped
  const size_t wit_size = witness.size ();
  vector<size_t> ws_index (wit_size);
  vector<size_t> skipped (wit_size);

  // if restoring[x] skipped[x] changes its meaning to the index for resizing.
  vector<bool> restoring (wit_size);
  // To decide whether a literal is still used as a witness 
  remaining.resize (wit_size, false); 

  // Every stack that has some entry should have a mark in witness.
  // There may also be only shared stacks with a given witness in their cubes so
  // we should not check '=='
  LOG ("witness.size () is %zu", wit_size);
  LOG ("witness_stacks.size () is %zu", witness_stacks.size ());
  //assert (witness.size () >= witness_stacks.size ());

  auto begin = witness_order.begin ();
  auto end = witness_order.end ();
  auto p = begin;
  auto q = p;

  while (p != end) {
    const int ewit = *p;
    
    if (ewit) { // regular witness entry
      const unsigned uwit = elit2ulit (ewit);
      size_t idx = ws_index[uwit]; 
      if (marked (tainted, -ewit) || internal->opts.restoreall == 2) { // need restoration
        auto &stack = witness_stacks[uwit];
        if (!marked (restoring, ewit)) { // possibly need index update
          assert (!idx);
          while (skipped[uwit]) {
            // proceed a clause in witness_stack[uwit]
            // 0 id_u id_l 0 l1 l2 ... lk 0
            // ^ ------------------------>^
            idx += 4; // now on the first literal
            assert (idx < stack.size ());
            assert (!stack[idx]);
            while (idx < stack.size () && stack[idx]) {
              ++idx;
            }
            --skipped[uwit];
          }
          skipped[uwit] = idx; // Now represents the cutoff for resizing
          mark (restoring, ewit);
        } 

        // idx is now on the first '0' of the clause to restore,
        // or at the end of the stack.
        if (idx != stack.size ()) {
          // restore clause at idx
          // 0 idu idl 0 l1 l2 .. lk
          const int64_t upper = stack[++idx];
          const int64_t lower = stack[++idx];
          const int64_t id = (upper << 32) + lower;
          assert (id);
          LOG ("id is %" PRId64, id);
          idx += 2; // idx should now be on the first literal
          auto cbegin = stack.begin () + idx;
          int satisfied = 0;
          while (idx < stack.size () && stack[idx]) {
            const int elit = stack[idx];
            if (!satisfied && fixed (elit) > 0)
              satisfied = elit;
            ++idx;
          }
          auto cend = stack.begin () + idx;
          // idx should now be at end of stack or on the first '0' of the next clause
          if (satisfied && !internal->opts.restoreflush) {
            LOG (cbegin, cend, "forced to not remove %d satisfied",
             satisfied);
            satisfied = 0;
          }
          if (satisfied) {
            LOG (cbegin, cend, 
               "flushing implied clause satisfied by %d from extension stack", 
               satisfied);
            clauses.satisfied++;
          } else {
            clauses.restored++;
            restore_clause (cbegin, cend, id);
          }
        }
        ws_index[uwit] = idx;
        ++p; // clause was restored
      } else {
        mark (remaining, ewit); // This clause will remain on the stack.
        *q++ = *p++;
      }

      continue;
    }
    // 0 ptr_u ptr_l 0
    // ^
    assert (p + 3 < end);
    assert (*(p + 3) == 0);
    const uintptr_t ptr =
          (static_cast<uintptr_t> (static_cast<uint32_t> (*(p + 1))) << 32) |
           static_cast<uint32_t> (*(p + 2));
    vector<int> *ss = reinterpret_cast<vector<int> *> (ptr);
    const bool ss_restored = restore_shared_stack (ss, clauses);
    if (ss_restored) {
      p += 4;
    } else {
      *q++ = *p++;
      *q++ = *p++;
      *q++ = *p++;
      *q++ = *p++;
    }
  }

  witness_order.resize (q - witness_order.begin ());
  // Resize all witness stacks that had restorations and update 'witness' marks.
  // 'skipped[i]' is the first position in the stack that was restored.
  for (size_t i = 0; i < witness.size (); i++) {
    if (i < witness_stacks.size ()) {
      auto &stack = witness_stacks[i];

      if (restoring[i])
        stack.resize (skipped[i]);

      assert (remaining[i] || stack.empty ());
    }

    if (!remaining[i]) 
      u_unmark (witness, i);
  }
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
  }
#endif

  if (!tainted.empty () || internal->opts.restoreall == 2) {
    
    // TODO: this does not account for shared stack sizes...
    for (const auto &s : witness_stacks)
      clauses.totalbytes += s.size () * sizeof (int);
    
    restore_in_order (clauses);

    // "resize" witness vector  
    while (!witness.empty () && !witness.back ())
      witness.pop_back ();
    // "resize" witness_stacks
    while (!witness_stacks.empty () &&
            witness_stacks.back ().empty ())
      witness_stacks.pop_back ();
  
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
  remaining.clear ();
  STOP (restore);
}
/*------------------------------------------------------------------------*/
} // namespace CaDiCaL
