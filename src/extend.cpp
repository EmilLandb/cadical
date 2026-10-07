#include "internal.hpp"

namespace CaDiCaL {

static constexpr uint32_t CLAUSE_SMALL = 1u << 31;
static constexpr uint32_t EMBEDDED     = 1u << 30;
static constexpr uint32_t ID_LONG     = 1u << 29;
static constexpr uint32_t SIZE_MASK   = (1u << 29) - 1;

void External::push_zero_on_extension_stack (int ewit) {
  assert (ewit);
  const unsigned uwit = elit2ulit (ewit);
  if (uwit >= witness_stacks.size ())
    witness_stacks.resize (uwit + 1); // the witness bitset is resized in mark
  witness_stacks[uwit].push_back (0);
  LOG ("pushing 0 on witness_stacks[%u] (external %d)", uwit, ewit);
}

void External::push_id_on_extension_stack (int ewit, int64_t id) {
  assert (ewit);
  const uint32_t higher_bits = static_cast<int> (id >> 32);
  const uint32_t lower_bits = (id & (((int64_t) 1 << 32) - 1));
  const unsigned uwit = elit2ulit (ewit);
  assert (uwit < witness_stacks.size ());
  witness_stacks[uwit].push_back (higher_bits);
  witness_stacks[uwit].push_back (lower_bits);
  LOG ("pushing id %" PRIu64 " = %d + %d on witness_stacks[%u] (external %d)", 
      id, higher_bits, lower_bits, uwit, ewit);
}

void External::push_clause_literal_on_extension_stack (int ewit, int ilit) {
  assert (ilit);
  assert (ewit);
  const int elit = internal->externalize (ilit);
  assert (elit);
  const unsigned uwit = elit2ulit (ewit);
  assert (uwit < witness_stacks.size ());
  witness_stacks[uwit].push_back (elit);
  LOG ("pushing clause literal %d on witness_stacks[%u] (external %d) (internal %d)", elit, 
       uwit, ewit, ilit);
}

// The extension stack allows to reconstruct a satisfying assignment for the
// original formula after removing eliminated clauses.  This was pioneered
// by Niklas Soerensson in MiniSAT and for instance is described in our
// inprocessing paper, published at IJCAR'12.  This first function adds a
// clause to this stack.  First the blocking or eliminated literal is added,
// and then the rest of the clause.
/* -------------------------------------------------------------------------- */
// NEW VERSION // _c
void External::push_clause_on_extension_stack (int wit, Clause *c) {
  assert (wit);
  LOG (c, "Pushing clause on extension stack");
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;
  
  const int ewit = internal->externalize (wit);
  assert (ewit);
  const unsigned uwit = elit2ulit (ewit);
  LOG ("ewit: %d, uwit: %u", ewit, uwit);
  if (uwit >= witness_stacks2.size ())
    witness_stacks2.resize (uwit + 1); // the witness bitset is resized in mark

  auto &stack = witness_stacks2[uwit];
  if (stack.empty ()) {
    // size | cap | es | idl | |C| - 1 | es
    const unsigned approx_min_size = 4 + c->size;
    stack.allocate (approx_min_size, arena);
  }
  // Remember the index of the first size field.
  stack.push_back (0, arena); // Will be updated in the end.
  const uint32_t first_size_field = stack.size () - 1;
  LOG ("pushing time stamp %u", stamp);
  // We can use the upper 3 bits for flagging if the clause has less than 
  // (1u << 29) - 1 litereals which is roughyl 536.9 million
  const unsigned size = c->size;
  const bool compactable = size < (1u << 29); 
  const bool id_long = c->id > UINT32_MAX; // does not fit into 32 bit

  const uint32_t idu = static_cast<uint32_t> (c->id >> 32);
  const uint32_t idl = static_cast<uint32_t> (c->id);
  // If we cannot flag or the id is just to long we push both parts.
  if (!compactable || id_long) {
    LOG ("pushing long id");
    stack.push_back (static_cast<int> (idu), arena);
    stack.push_back (static_cast<int> (idl), arena);
  } else {
    assert (!idu);
    LOG ("pushing compact id");
    stack.push_back (static_cast<int> (idl), arena);
  }

  // Now we will push the literals. 
  // We will skip the witness if it is embeddable, i.e. if the clause is
  // compactable and the witness is included in the clause
  bool embedded = false;
  for (const auto &lit : *c) {
    const int elit = internal->externalize (lit);
    if (elit == ewit)
      if (compactable) {
        embedded = true;
        continue;
      }
    LOG ("pushing literal %d (external %d)", lit, elit);
    stack.push_back (elit, arena);
  }

  // Finally we update the size fields accordingly.
  uint32_t updated_size = c->size;
  if (embedded) {
    updated_size--; // One literal less in the literals field.
    updated_size |= EMBEDDED; 
  }
  if (compactable) {
    updated_size |= CLAUSE_SMALL;
    if (id_long)
      updated_size |= ID_LONG;
  }
  // Update the first size field and push the terminating size field.
  stack.stack[first_size_field] = static_cast<int> (updated_size);
  stack.push_back (static_cast<int> (updated_size), arena);
  LOG (stack.begin (), static_cast<unsigned> (stack.end () - stack.begin ()), "stack now: ");
  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }

  witness_order.push_back (ewit);
}

// NEW VERSION // _c
void External::push_binary_clause_on_extension_stack (int64_t id, int wit, 
                                                      int other) {
  LOG ("pushing binary clause[%" PRId64 "] %d %d on extension stack", id, wit, other);
  internal->stats.weakened++;
  internal->stats.weakened_lengths += 2;

  const int ewit = internal->externalize (wit);
  assert (ewit);
  const unsigned uwit = elit2ulit (ewit);

  if (uwit >= witness_stacks2.size ())
    witness_stacks2.resize (uwit + 1); // the witness bitset is resized in mark

  auto &stack = witness_stacks2[uwit];
  stack.push_back (0, arena);
  const uint32_t first_size_field = stack.size () - 1;
  
  const bool id_long = id > UINT32_MAX;
  const uint32_t idu = static_cast<uint32_t> (id >> 32);
  const uint32_t idl = static_cast<uint32_t> (id);

  if (id_long) {
    stack.push_back (static_cast<int> (idu), arena);
    stack.push_back (static_cast<int> (idl), arena);
  } else {
    assert (!idu);
    stack.push_back (static_cast<int> (idl), arena);
  }

  // Here we can definitely make use of witness embedding.
  const int elit = internal->externalize (other);
  stack.push_back (elit, arena);

  uint32_t updated_size = 1;
  updated_size |= EMBEDDED;
  updated_size |= CLAUSE_SMALL;

  if (id_long)
    updated_size |= ID_LONG;

  stack.stack[first_size_field] = static_cast<int> (updated_size);
  stack.push_back (static_cast<int> (updated_size), arena);

  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }

  witness_order.push_back (ewit);
}

/* -------------------------------------------------------------------------- */
uint32_t External::create_shared_stack (const vector<int> &iwit_cube) {
  
  const uint32_t ss_idx = shared_stacks.allocate ();
  assert (ss_idx <= UINT32_MAX);

  SharedStack &ss = shared_stacks[ss_idx];
  assert (!ss.data.stack);

  const unsigned initial_size = iwit_cube.size() + 3; // size, cap, cube, 0
  ss.data.allocate (initial_size, arena);

  ss.backlinks = 0;

  // push a reference to all witness stacks of literals in the cube
  // First we push the cube to the data stack then we delimit by '0' and 
  // can continue to push clauses.
  // data: w1 w2 ... wk 0 EC1 EC2 .. ECl
  for (const auto &iwit : iwit_cube) {
    const int ewit = internal->externalize (iwit);
    assert (ewit);
    const unsigned uwit = elit2ulit (ewit);

    ss.push_back (ewit, arena);

    if (uwit >= witness_stacks2.size ())
      witness_stacks2.resize (uwit + 1);
    if (!marked (witness, ewit))
      mark (witness, ewit);

    WitnessStack &stack = witness_stacks2[uwit];
    // Push the reference to the corresponding witness stack: 0 ss_idx
    stack.push_back (0, arena);
    stack.push_back (ss_idx, arena);
    ss.backlinks++;
  }
  // delimit witness cube by zero
  ss.push_back (0, arena);
  return ss_idx;
}

void External::push_shared_clause (uint32_t ss_idx, Clause *c) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;

  SharedStack &ss = shared_stacks[ss_idx];
  // We use a similar encoding as for regular clause entries.
  // We do not need to push a time stamp for every clause since it is shared.
  // Also we will not attempt to embedd the witness cube in the clause for now.
  // es (idu) idl l1 ... lk es
  ss.push_back (0, arena); // Will be updated in the end.
  const uint32_t first_size_field = ss.data.size () - 1;
  // no need to push a stamp here.

  const unsigned size = c->size;
  const bool compactable = size < (1u << 29);
  const bool id_long = c->id > UINT32_MAX;

  const uint32_t idu = static_cast<int> (c->id >> 32);
  const uint32_t idl = (c->id & (((int64_t) 1 << 32) - 1));

  if (!compactable || id_long) {
    LOG ("pushing long id");
    ss.push_back (static_cast<int> (idu), arena);
    ss.push_back (static_cast<int> (idl), arena);
  } else {
    LOG ("pushing compact id");
    ss.push_back (static_cast<int> (idl), arena);
  }

  // Now we will push the literals.
  for (const auto &ilit : *c) {
    assert (ilit);
    const int elit = internal->externalize (ilit);
    assert (elit);
    ss.push_back (elit, arena);
  }
  
  // Finally we update the size fields accordingly;
  uint32_t updated_size = c->size;
  if (compactable && id_long) {
    updated_size |= CLAUSE_SMALL;
    updated_size |= ID_LONG;
  }
  ss.data[first_size_field] = static_cast<int> (updated_size);
  ss.push_back (static_cast<int> (updated_size), arena);
}

void External::create_shared_stack_and_push_clause (
    const vector<int> &iwit_cube, Clause *c) {
  LOG ("Creating a shared stack for a single clause with witness cube.");

  const uint32_t ss_idx = shared_stacks.allocate ();
  assert (ss_idx <= UINT32_MAX);

  SharedStack &ss = shared_stacks[ss_idx];
  assert (!ss.data.stack);
  // size cap | cube literals | 0 | es | idl | clause literals | es
  const unsigned initial_size = 2 + iwit_cube.size () + 3 + c->size + 1;
  ss.data.allocate (initial_size, arena);

  ss.backlinks = 0;

  push_shared_clause (ss_idx, c);
}

/*------------------------------------------------------------------------*/
// TODO: This needs updating
// the calls to init are used in the copy test, should never trigger during
// actual solver runtime.
void External::push_external_clause_and_witness_on_extension_stack (
    const vector<int> &c, const vector<int> &w, int64_t id) {
  assert (id);
  extension.push_back (0);
  for (const auto &elit : w) {
    assert (elit != INT_MIN && elit);
    assert (abs (elit) <= max_var);
    int eidx = abs (elit);
    if (!e2i[eidx])
      init (eidx);
    assert (e2i[eidx] && e2i[eidx] != INT_MIN);
    extension.push_back (elit);
    mark (witness, elit);
  }
  extension.push_back (0);
  const uint32_t higher_bits = static_cast<int> (id << 32);
  const uint32_t lower_bits = (id & (((int64_t) 1 << 32) - 1));
  extension.push_back (higher_bits);
  extension.push_back (lower_bits);
  extension.push_back (0);
  for (const auto &elit : c) {
    assert (elit != INT_MIN);
    assert (abs (elit) <= max_var);
    int eidx = abs (elit);
    if (!e2i[eidx])
      init (abs (eidx));
    assert (e2i[eidx] && e2i[eidx] != INT_MIN);
    extension.push_back (elit);
  }
}

/*------------------------------------------------------------------------*/
inline void decode_size_field (const int size_field, bool &wit_embedded, 
                               bool &id_long, unsigned &other_lits_size) {
  assert (size_field);

  const uint32_t encoded = static_cast<uint32_t> (size_field);
  const bool clause_small = encoded & CLAUSE_SMALL;

  wit_embedded = clause_small && (encoded & EMBEDDED);
  id_long = !clause_small || (encoded & ID_LONG);
  other_lits_size = clause_small ? (encoded & SIZE_MASK) : encoded;
}

/*------------------------------------------------------------------------*/
// TODO: Update description
// This is the actual extension process. It goes backward over the clauses
// on the extension stack and flips the assignment of one of the blocking
// literals in the conditional autarky stored before the clause.  In the
// original algorithm for witness construction for variable elimination and
// blocked clause removal the conditional autarky consists of a single
// literal from the removed clause, while in general the autarky witness can
// contain an arbitrary set of literals.  We are using the more general
// witness reconstruction here which for instance would also work for
// super-blocked or set-blocked clauses.
/*
void External::extend_shared_stack (int *p, unsigned uwit, ExtendStats &stats) {
  LOG ("Extending shared stack with witness cube");
    
  assert (!*(p - 2));
  uint32_t ss_idx = static_cast<uint32_t> (*(p - 1));
  SharedStack &ss = shared_stacks[ss_idx];

  if (ss.empty ()) // Stale entry.
    return;

#ifndef QUIET
  stats.extension_size += ss.data.size ();
#endif

  bool satisfied = true;
  auto q = ss.begin ();
  auto end_of_stack = ss.end ();

  // first check the cube for being satisfied. Also check if this stack has been
  // already been scheduled for extension.
  while (*q) {
    const int ewit = *q++;
    const unsigned other_uwit = elit2ulit (ewit);
    if (other_uwit != uwit &&
        priority[other_uwit] &&
        priority[other_uwit] <= ss.stamp) {
      satisfied = true;
      break;
    } 
    // some witness falsified or unassigned
    if (ival (ewit) != ewit)
      satisfied = false;
  }

  if (satisfied) {
    LOG ("Shared stack clauses are skipped. (already scheduled or satisfied)");
    return;
  }

  // The witness cube is not fully assigned. Therefore we need to check for
  // unsatisfied clauses.
  auto begin_of_clauses = q + 1; // this should be the first size field
  q = end_of_stack;
  bool assign_witness = false;
  while (q != begin_of_clauses) {
    q--; // q now points to the trailing size field
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (q, wit_embedded, id_long, other_lits_size);
    assert (!wit_embedded);
    assert (other_lits_size);

    q--; // q points to the last literal now

    auto idl_pos = q - other_lits_size;
    bool satisfied = false;

    while (q != idl_pos) {
      const int elit = *q;
      if (!satisfied && ival (elit) == elit)
        satisfied = true;
      --q;
    }
    // q should now point to the idl field.
    // assign the cube.
    if (!satisfied) {
      assign_witness = true;
      break;
    }
    // es (idu) idl
    //           q
    q -= (id_long ? 1 : 0) + 1;
  }

  if (assign_witness) {
    q = ss.begin ();
    while (*q) {
      const int ewit = *q++;
      if (ival (ewit) == ewit)
        continue;
      LOG ("flipping witness literal %d", ewit);
      assert (ewit);
      assert (ewit != INT_MIN);
      size_t idx = abs (ewit);
      if (idx >= vals.size ())
        vals.resize (idx + 1, false);
      vals[idx] = !vals[idx];
      internal->stats.extended++;
#ifndef QUIET
      stats.flipped++;
#endif 
    }
  }
}
*/
/* -------------------------------------------------------------------------- */
/* -------------------------------------------------------------------------- */
// extend the next clause to be extended on the witness stack of ewit 
// and update index to the next clause to be extended on this stack.
void External::extend_next (const int ewit, ExtendStats &stats) {
  const unsigned uwit = elit2ulit (ewit);
  WitnessStack &stack = witness_stacks2[uwit];  

  uint32_t idx = ws_index[uwit] - 1; // idx to the trailing size field
  assert (idx);

  const int size_field = stack[idx];
  
  bool wit_embedded, id_long;
  unsigned other_lits_size;
  decode_size_field (size_field, wit_embedded, id_long, other_lits_size);
  assert (other_lits_size);
  --idx; // idx to the last literal
  auto idl_pos = idx - other_lits_size;
  bool satisfied = false;

  while (idx != idl_pos) {
    const int elit = stack[idx];
    if (!satisfied && ival (elit) == elit)
      satisfied = true;
    --idx;
  }

  // idx should now be of the idl field
  if (!satisfied) {
    if (wit_embedded)
      if (ival (ewit) == ewit)
        satisfied = true;
  }
  if (!satisfied) {
    assert (ival (ewit) != ewit);
    const size_t var = abs (ewit);
    if (var >= vals.size ())
      vals.resize (var + 1, false);
    vals[var] = !vals[var];
    internal->stats.extended++;
#ifndef QUIET
    stats.flipped++;
#endif 
  }
  idx -= (id_long ? 1 : 0) + 1; // idx is of the first size field.
  ws_index[uwit] = idx;
}

// NEW VERSION // _c
void External::extend () {
  assert (!extended);
  PROFILE_SCOPE (extend);
  internal->stats.extensions++;
  
  PHASE ("extend", internal->stats.extensions,
         "mapping internal %d assignments to %d assignments",
         internal->max_var, max_var);

  ExtendStats stats = {};

  // Copy the internal assignment into an external one
  for (unsigned i = 1; i <= (unsigned) max_var; i++) { 
    const int ilit = e2i[i];
    if (!ilit)
      continue;
    if (i >= vals.size ())
      vals.resize (i + 1, false);
    vals[i] = (internal->val (ilit) > 0);
#ifndef QUIET
    stats.updated++;
#endif
  }

  // Initialize the extension state.
  assert (ws_index.empty ());
  ws_index.resize (witness_stacks2.size ());

  // initialize the indices into the stacks
  for (unsigned uwit = 0; uwit < witness_stacks2.size (); uwit++) {
    WitnessStack &stack = witness_stacks2[uwit];
    if (stack.empty ())
      continue;
#ifndef QUIET
    stats.extension_size += stack.size () - 2;
#endif
    const uint32_t stack_size = stack.size () - 2; // ignore size & capacity
    ws_index[uwit] = stack_size;
  }
  
  auto p = witness_order.end ();
  auto begin = witness_order.begin ();

  while (p != begin) {
    // TODO: lookahead one, if it is a zero extend shared stack instead
    const int ewit = *--p;
    extend_next (ewit, stats);
  }

  ws_index.clear ();


  internal->stats.extension_events += stats.events;
  internal->stats.extension_heap_pushed += stats.pushed;
  PHASE ("extend", internal->stats.extensions,
         "extended through extension stack of size %lld", stats.extension_size);
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", stats.flipped);
  extended = true;
  LOG ("extended");
}

/* -------------------------------------------------------------------------- */
/* -------------------------------------------------------------------------- */
/*
bool External::traverse_shared_stack_backward (WitnessIterator &it, int *p, unsigned uwit) {
  assert (!*(p - 2));
  uint32_t ss_idx = static_cast<uint32_t> (*(p - 1));
  SharedStack &ss = shared_stacks[ss_idx];
  if (ss.empty ()) // State entry
    return true;

  vector<int> witness;
  auto q = ss.begin ();

  while (*q) {
    const int ewit = *q++;
    const unsigned other_uwit = elit2ulit (ewit);
    if (other_uwit != uwit && priority[other_uwit] <= ss.stamp)
      return true;
    witness.push_back (ewit);
  }
  
  auto begin_of_clauses = q + 1; // first size field of first clause
  q = ss.end ();
  vector<int> clause;
  while (q != begin_of_clauses) {
    q--; // q now points to the trailing size field
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (q, wit_embedded, id_long, other_lits_size);
    assert (!wit_embedded);
    assert (other_lits_size);

    q--; // q points to the last literal now

    auto idl_pos = q - other_lits_size;

    clause.clear ();
    while (q != idl_pos) {
      clause.push_back (*q--);
    }
    int64_t id;
    if (id_long) {
      const uint64_t upper = static_cast<uint32_t> (*(q - 1));
      const uint64_t lower = static_cast<uint32_t> (*q);
      id = static_cast<int64_t> ((upper << 32) | lower);
      q -= 2;
    } else {
      id = static_cast<uint32_t> (*q);
      q--;
    }
    assert (id);
    
    // q points to the first size field.
    reverse (clause.begin (), clause.end ());

    if (!it.witness (clause, witness, id)) {
      return false;
    }
  }
  return true;
}

bool External::traverse_shared_stack_forward (WitnessIterator &it, int *p, unsigned uwit) {
  assert (!*p);
  uint32_t ss_idx = static_cast<uint32_t> (*(p + 1));
  SharedStack &ss = shared_stacks[ss_idx];
  if (ss.empty ())
    return true;

  vector<int> witness;
  auto q = ss.begin ();

  while (*q) {
    const int ewit = *q++;
    const unsigned other_uwit = elit2ulit (ewit);
    if (other_uwit != uwit && priority[other_uwit] <= ss.stamp)
      return true;
    witness.push_back (ewit);
  }

  q++; // q points to the first size field of the first clause.
  auto end = ss.end ();
  vector<int> clause;
  while (q != end) {
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (q, wit_embedded, id_long, other_lits_size);
    assert (!wit_embedded);
    assert (other_lits_size);

    int64_t id;
    if (id_long) {
      const uint64_t upper = static_cast<uint32_t> (*(q + 1));
      const uint64_t lower = static_cast<uint32_t> (*(q + 2));
      id = static_cast<int64_t> ((upper << 32) | lower );
      q += 3;
    } else {
      id = static_cast<uint32_t> (*q);
      q += 2;
    }

    auto end_of_lits = q + other_lits_size;
    clause.clear ();
    while (q != end_of_lits) {
      clause.push_back (*q++);
    }
    // q points to the trailing size field

    reverse (clause.begin (), clause.end ());

    if (!it.witness (clause, witness, id)) {
      return false;
    }
    q++; // q points to the next clauses first size field or end of stack
  }
  return true;
}
*/

bool External::traverse_witnesses_backward (WitnessIterator &it) {
  if (internal->unsat)
    return true;

  assert (ws_index.empty ());
  ws_index.resize (witness_stacks2.size ());

  for (unsigned uwit = 0; uwit < witness_stacks2.size (); uwit++) {
    WitnessStack &stack = witness_stacks2[uwit];
    if (stack.empty ())
      continue;
    const uint32_t stack_size = stack.size () - 2; // ignore size & capacity
    ws_index[uwit] = stack_size;
  }

  vector<int> clause, witness;

  auto p = witness_order.end ();

  while (p != witness_order.begin ()) {
    const int ewit = *--p;
    const unsigned uwit = elit2ulit (ewit);
    auto &stack = witness_stacks2[uwit];

    uint32_t idx = ws_index[uwit];
    assert (idx);
    auto q = stack.begin () + idx; // one beyond the trailing size field
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    q--;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);

    witness.clear ();
    witness.push_back (ewit);

    q--; // q points to the last literal of the clause.
    auto idl_pos = q - other_lits_size;
    clause.clear ();
    while (q != idl_pos) {
      clause.push_back (*q--);
    }
    if (wit_embedded)
      clause.push_back (ewit);
    // q points to idl
    int64_t id;
    if (id_long) {
      const uint64_t upper = static_cast<uint32_t> (*(q - 1));
      const uint64_t lower = static_cast<uint32_t> (*q);
      id = static_cast<int64_t> ((upper << 32) | lower);
      q -= 2;
    } else {
      id = static_cast<uint32_t> (*q);
      q --;
    }
    assert (id);
    reverse (clause.begin (), clause.end ());
    if (!it.witness (clause, witness, id)) {
      ws_index.clear ();
      ws_index.shrink_to_fit ();
      return false;
    }
    ws_index[uwit] = q - stack.begin ();
  }
  ws_index.clear ();
  ws_index.shrink_to_fit ();
  return true;
}

bool External::traverse_witnesses_forward (WitnessIterator &it) {
  if (internal->unsat)
  return true;

  assert (ws_index.empty ());
  ws_index.resize (witness_stacks2.size ());

  vector<int> clause, witness;
  auto p = witness_order.begin ();

  while (p != witness_order.end ()) {
    const int ewit = *p++;
    const unsigned uwit = elit2ulit (ewit);
    auto &stack = witness_stacks2[uwit];

    uint32_t idx = ws_index[uwit];
    assert (idx < stack.size () - 2); 

    auto q = stack.begin () + idx; // on the first size field of the next clause
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (*q, wit_embedded, id_long, other_lits_size);

    witness.clear ();
    witness.push_back (ewit);
    int64_t id;
    if (id_long) {
      const uint64_t upper = static_cast<uint32_t> (*(q + 1));
      const uint64_t lower = static_cast<uint32_t> (*(q + 2));
      id = static_cast<int64_t> ((upper << 32) | lower);
      q += 3;
    } else {
      id = static_cast<uint32_t> (*(q + 1));
      q += 2;
    }
    // q points to the first literal of the clause

    auto end_of_lits = q + other_lits_size; 
    clause.clear ();
    if (wit_embedded)
      clause.push_back (ewit);
    while (q != end_of_lits) {
      clause.push_back (*q++);
    }
    
    if (!it.witness (clause, witness, id)) {
      ws_index.clear ();
      ws_index.shrink_to_fit ();
      return false;
    }
    q++; // q points to the next clauses first size field
    ws_index[uwit] = q - stack.begin ();
  }
  ws_index.clear ();
  ws_index.shrink_to_fit ();
  return true;
}

/*------------------------------------------------------------------------*/

void External::conclude_sat () {
  if (!internal->proof || concluded)
    return;
  concluded = true;
  if (!extended)
    extend ();
  vector<int> model;
  for (int idx = 1; idx <= max_var; idx++) {
    if (ervars[idx])
      continue;
    const int lit = ival (idx);
    model.push_back (lit);
  }
  internal->proof->conclude_sat (model);
}

} // namespace CaDiCaL
