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

inline void decode_size_field (vector<int>::const_iterator size_field, bool &wit_embedded, 
                               bool &id_long, unsigned &other_lits_size) {
  assert (*size_field);

  const uint32_t encoded = static_cast<uint32_t> (*size_field);
  const bool clause_small = encoded & CLAUSE_SMALL;

  wit_embedded = clause_small && (encoded & EMBEDDED);
  id_long = !clause_small || (encoded & ID_LONG);
  other_lits_size = clause_small ? (encoded & SIZE_MASK) : encoded;
}

/*------------------------------------------------------------------------*/

void External::restore_clause (const vector<int>::const_iterator &begin,
                               const vector<int>::const_iterator &end,
                               const int64_t id, const bool wit_embedded) {
  LOG (begin, end, "restoring external clause[%" PRId64 "]", id);
  assert (eclause.empty ());
  assert (id);
  auto p = begin;
  if (wit_embedded)
    ++p;
  for (; p != end; p++) {
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

  if (wit_embedded) {
    const int ewit = *begin;
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
    internal->add_original_lit (ilit);
    internal->stats.restored_literals++;
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

/*------------------------------------------------------------------------*/
// NEW VERSION
void External::restore_clauses () {
  assert (internal->opts.restoreall == 2 || !tainted.empty ());

  PROFILE_SCOPE (restore);
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

  LOG ("NEW restore_clauses ENTERED, extension size %zu", extension.size ());
  auto end_of_extension = extension.end ();
  auto p = extension.begin (), q = p;
  while (p != end_of_extension) {
    LOG ("NEW restore_clauses INSIDE LOOP");
    clauses.weakened++;

    const auto saved = q;

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (p, wit_embedded, id_long, other_lits_size);
    
    int64_t id;

    if (id_long) {
      const uint64_t upper = static_cast<uint32_t> (*(p + 1));
      const uint64_t lower = static_cast<uint32_t> (*(p + 2));
      id = static_cast<int64_t> ((upper << 32) | lower);
    } else {
      id = static_cast<uint32_t> (*(p + 1));
    }
    LOG ("id is %" PRId64, id);
    assert (id);

    auto wit = p + (id_long ? 3 : 2);
    auto begin_of_lits = wit + 1;
    auto end_of_lits = begin_of_lits + other_lits_size;
    auto end_of_entry = end_of_lits + 1; // trailing encode size field

    assert (end_of_entry <= end_of_extension);

    int tlit = 0;
    if (marked (tainted, -*wit)) {
      tlit = *wit;
      LOG ("negation of witness literal %d tainted", tlit);
    }

    int satisfied = 0;

    for (auto r = begin_of_lits; r != end_of_lits; ++r) {
      if (!satisfied && fixed (*r) > 0)
        satisfied = *r;
    }

    if (wit_embedded && !satisfied && fixed (*wit) > 0)
      satisfied = *wit;

    if (satisfied && !internal->opts.restoreflush)
      satisfied = 0;

    if (satisfied || tlit || internal->opts.restoreall) {
      if (satisfied) {
        clauses.satisfied++;
      } else {
        auto clause_begin = wit_embedded ? wit : begin_of_lits;
        restore_clause (clause_begin, end_of_lits, id, wit_embedded);
        clauses.restored++;
      }

      clauses.removed++;
      p = end_of_entry;
      q = saved;
    } else {
      while (p != end_of_entry)
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
    --p;

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (p, wit_embedded, id_long, other_lits_size);
    // es (idu) idl wit l1 .. lk es
    // p points at trailing size field.
    // Move backwards over stored literals
    p--;
    p -= other_lits_size;

    // p now points at witness
    const int ewit = *p;

    mark (witness, ewit);

    // Move from witness back to the initial size field.
    p -= id_long ? 3 : 2;
  }

}

void External::restore_clauses_c () {

  assert (internal->opts.restoreall == 2 || !tainted.empty ());

  PROFILE_SCOPE (restore);
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
    const int64_t id = ((int64_t) (*p) << 32) + (int64_t) * (p + 1);
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
        //restore_clause (p, end_of_clause, id); // Might taint literals.
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
}

} // namespace CaDiCaL
