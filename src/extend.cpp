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

void External::push_stamp_on_extension_stack (int ewit) {
  assert (ewit);
  const unsigned uwit = elit2ulit (ewit);
  assert (uwit < witness_stacks.size ());
  witness_stacks[uwit].push_back (++stamp);
  LOG ("pushing time stamp %u on witness_stacks[%u] (external %d)", stamp, uwit, ewit);
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
  // Remember the index of the first size field.
  stack.push_back (0); // Will be updated in the end.
  const uint32_t first_size_field = stack.size () - 1;
  stack.push_back (++stamp);
  LOG ("pushing time stamp %u", stamp);
  // We can use the upper 3 bits for flagging if the clause has less than 
  // ~540 million literals.
  const unsigned size = c->size;
  const bool compactable = size < (1u << 29); 
  const bool id_long = c->id > UINT32_MAX; // does not fit into 32 bit

  const uint32_t idu = static_cast<uint32_t> (c->id >> 32);
  const uint32_t idl = static_cast<uint32_t> (c->id);
  // If we cannot flag or the id is just to long we push both parts.
  if (!compactable || id_long) {
    LOG ("pushing long id");
    stack.push_back (static_cast<int> (idu));
    stack.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    LOG ("pushing compact id");
    stack.push_back (static_cast<int> (idl));
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
    stack.push_back (elit);
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
  stack.push_back (static_cast<int> (updated_size));
  LOG (stack.begin (), static_cast<unsigned> (stack.end () - stack.begin ()), "stack now: ");
  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }
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
  stack.push_back (0);
  const uint32_t first_size_field = stack.size () - 1;
  
  stack.push_back (++stamp);

  const bool id_long = id > UINT32_MAX;
  const uint32_t idu = static_cast<uint32_t> (id >> 32);
  const uint32_t idl = static_cast<uint32_t> (id);

  if (id_long) {
    stack.push_back (static_cast<int> (idu));
    stack.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    stack.push_back (static_cast<int> (idl));
  }

  // Here we can definitely make use of witness embedding.
  const int elit = internal->externalize (other);
  stack.push_back (elit);

  uint32_t updated_size = 1;
  updated_size |= EMBEDDED;
  updated_size |= CLAUSE_SMALL;

  if (id_long)
    updated_size |= ID_LONG;

  stack.stack[first_size_field] = static_cast<int> (updated_size);
  stack.push_back (static_cast<int> (updated_size));

  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }
}

/* -------------------------------------------------------------------------- */
// Push a clauses id and literals on witness stack x
/*
void External::push_clause_on_extension_stack (int wit, Clause *c) {
  assert (wit);
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;

  const int ewit = internal->externalize (wit);
  assert (ewit);
  
  push_zero_on_extension_stack (ewit);
  push_stamp_on_extension_stack (ewit);
  push_id_on_extension_stack (ewit, c->id);
  push_zero_on_extension_stack (ewit);
  for (const auto &lit : *c)
    push_clause_literal_on_extension_stack (ewit, lit);
  
  // Now also mark the witness
  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }
}

void External::push_binary_clause_on_extension_stack (int64_t id, int wit,
                                                      int other) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += 2;

  const int ewit = internal->externalize (wit);
  assert (ewit);

  push_zero_on_extension_stack (ewit);
  push_stamp_on_extension_stack (ewit);
  push_id_on_extension_stack (ewit, id);
  push_zero_on_extension_stack (ewit);
  push_clause_literal_on_extension_stack (ewit, wit);
  push_clause_literal_on_extension_stack (ewit, other);

  // Mark the witness
  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }
}
*/
External::SharedStack* External::create_shared_stack (const vector<int> &iwit_cube) {
  
  SharedStack *ss = new SharedStack;
  
  ss->backlinks = 0;
  ss->stamp = ++stamp;

  const uintptr_t ptr = reinterpret_cast<uintptr_t> (ss);
  const int upper = static_cast<int> (ptr >> 32);
  const int lower = static_cast<int> (ptr & 0xffffffff);

  // push a reference to all witness stacks of literals in the cube
  for (const auto &iwit : iwit_cube) {
    const int ewit = internal->externalize (iwit);
    assert (ewit);
    const unsigned uwit = elit2ulit (ewit);

    ss->witness_cube.push_back (ewit);

    if (uwit >= witness_stacks.size ())
      witness_stacks.resize (uwit + 1);
    if (!marked (witness, ewit))
      mark (witness, ewit);

    vector<int> &stack = witness_stacks[uwit];

    // 0 0 0 p_u p_l
    stack.push_back (0);
    stack.push_back (0);
    stack.push_back (0);
    stack.push_back (upper);
    stack.push_back (lower);

    ss->backlinks++;
  }
  return ss;
}

void External::push_shared_clause (SharedStack *ss, Clause *c) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;

  vector<int> &stack = ss->clause_data;

  const uint32_t higher_bits = static_cast<int> (c->id >> 32);
  const uint32_t lower_bits = (c->id & (((int64_t) 1 << 32) - 1));
  // 0 id_u id_l 0 l1 l2 .. lk
  stack.push_back (0);
  LOG (ss->witness_cube, "pushing id %" PRIu64 " = %d + %d on shared stack ", 
       c->id, higher_bits, lower_bits);
  stack.push_back (higher_bits);
  stack.push_back (lower_bits);
  stack.push_back (0);
  for (const auto &ilit : *c) {
    assert (ilit);
    const int elit = internal->externalize (ilit);
    assert (elit);
    stack.push_back (elit);
    LOG ("pushing clause literal %d (internal %d) on shared stack", 
          elit, ilit);
  }
}

void External::create_shared_stack_and_push_clause (
    const vector<int> &iwit_cube, Clause *c) {
  LOG ("Creating a shared stack for a single clause with witness cube.");
  SharedStack *ss = create_shared_stack (iwit_cube);
  push_shared_clause (ss, c);
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
inline void decode_size_field (const int *size_field, bool &wit_embedded, 
                               bool &id_long, unsigned &other_lits_size) {
  assert (*size_field);

  const uint32_t encoded = static_cast<uint32_t> (*size_field);
  const bool clause_small = encoded & CLAUSE_SMALL;

  wit_embedded = clause_small && (encoded & EMBEDDED);
  id_long = !clause_small || (encoded & ID_LONG);
  other_lits_size = clause_small ? (encoded & SIZE_MASK) : encoded;
}

uint32_t External::r_timestamp (const vector<int> &stack, uint32_t idx) {
  assert (idx <= stack.size ());
  assert (idx);
  // case 1 shared stack: 0 0 0 ptr_u ptr_l .
  //                                        ^
  if (idx >= 5 &&
      !stack[idx - 5] &&
      !stack[idx - 4] &&
      !stack[idx - 3]) {
    LOG ("r_timestamp shared clause detected.");
    const uintptr_t ptr = (static_cast<uintptr_t> (
                          static_cast<uint32_t> (stack[idx - 2])) << 32) |
                          static_cast<uint32_t> (stack[idx - 1]);
    SharedStack *ss = reinterpret_cast<SharedStack *> (ptr);
    return ss->stamp; 
  }
  // case 2 regular: 0 ts idu idl 0 l1 .. lk .
  //                                         ^
  uint32_t p = idx - 1; // last literal of the clause
  while (stack[p])
    --p;
  // p is on the 0 after the literals
  assert (p >= 4);
  assert (!stack[p]);
  assert (!stack[p - 4]);
  return static_cast<uint32_t> (stack[p - 3]);
}

// NEW VERSION
uint32_t External::r_timestamp_c (int *p) {
  bool wit_embedded, id_long;
  unsigned other_lits_size;
  decode_size_field (p - 1, wit_embedded, id_long, other_lits_size);
  // es ts (idu) idl l1 ... lk es [end/es2]
  //                                 p
  const uint32_t ts = *(p - 2 - other_lits_size - (id_long ? 2 : 1));
  assert (ts);
  return ts;
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

void External::extend_shared_stack (SharedStack *ss, unsigned uwit, ExtendStats &stats) {
  LOG (ss->witness_cube, "Extending shared stack of size %zu with witness cube", 
       ss->clause_data.size ());
#ifndef QUIET
  stats.extension_size += ss->witness_cube.size ();
  stats.extension_size += ss->clause_data.size ();
#endif
  

  // first check the cube for being satisfied. Also check if this stack has been
  // already been scheduled for extension.
  vector<int> &witness_cube = ss->witness_cube;
  bool satisfied = true;
  for (const auto &ewit : witness_cube) {
    // check if the shared stack was already extended
    const unsigned other_uwit = elit2ulit (ewit);
    if (other_uwit != uwit && 
        priority[other_uwit] &&
        priority[other_uwit] <= ss->stamp) { 
      satisfied = true;
      break;
    }

    if (ival (ewit) != ewit)  // Witness falsified
      satisfied = false;
  }
  if (satisfied) {
    LOG ("Shared stack clauses are skipped. (already scheduled or satisfied)");
    return;
  }
  // The witness cube is not fully assigned. Therefore we need to check for
  // unsatisfied clauses.
  vector<int> &stack = ss->clause_data;
  auto p = stack.end ();
  auto begin = stack.begin ();
  bool assign_witness = false;
  // 0 id_u id_l 0 l1 l2 ... lk
  // ^
  while (p != begin) {
    // p is at end of stack or the first 0 of the previous clause
    bool clause_satisfied = false;
    while (*--p) { // go through all literals
      int elit = *p;
      // If lit is satisfied we can just skip the clause
      if (ival (elit) == elit)
        clause_satisfied = true;
    }
    // We have found a clause that is not satisfied -> assign the witness
    if (!clause_satisfied) {
      assign_witness = true;
      break;
    }
    // 0 id_u id_l 0
    //             ^ 
    p -= 3;
  }

  if (assign_witness) {
    for (const auto &ewit : witness_cube) {
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

// NEW VERSION
void External::extend_next_c (unsigned uwit, ExtendHeap &extend_heap, 
                              ExtendStats &stats) {
  WitnessStack &stack = witness_stacks2[uwit];
  uint32_t idx = ws_index[uwit];
  uint32_t ts = 0;
  auto p = stack.begin () + idx;
  while (p != stack.begin ()) {
    // TODO: update to also support shared stack references.
    ts = r_timestamp_c (p);
    
    p--; // p now points to the trailing size field

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (p, wit_embedded, id_long, other_lits_size);
    assert (other_lits_size);

    p--; // p points to the last literal now

    auto idl_pos = p - other_lits_size;
    bool satisfied = false;

    while (p != idl_pos) {
      const int elit = *p;
      if (!satisfied && ival (elit) == elit)
        satisfied = true;
      --p;
    }

    // p should now point to the idl field.
    if (!satisfied) {
      const int sign = (int) (uwit & 1);
      const int ewit = ((int) (uwit >> 1) + 1 ^ -sign) + sign;
      LOG ("ewit %d computed from uwit %u", ewit, uwit);
      if (wit_embedded) { // still need to check the witness literal
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
    }
    stats.events++;
    p -= (id_long ? 1 : 0) + 1 + 1; // p points to the first size field.
    if (!extend_heap.empty () &&
        ts < priority[extend_heap.top ()])
      break;
  }
  // update idx
  ws_index[uwit] = p - stack.begin ();
  if (p != stack.begin ()) { // reschedule if the stack is not empty
    priority[uwit] = ts;
    extend_heap.push (uwit);
#ifndef QUIET
      stats.pushed++;
#endif
  }
}

void External::extend_next (unsigned uwit, ExtendHeap &extend_heap, 
                            ExtendStats &stats) {
  vector<int> &stack = witness_stacks[uwit];
  uint32_t idx = ws_index[uwit];
  uint32_t ts = 0;  
  while (idx) {
    assert (idx >= 5);
    const bool shared_ref = !stack[idx - 3] && 
                            !stack[idx - 4] && 
                            !stack[idx - 5];                        
    if (shared_ref) {
      const uintptr_t ptr =  (static_cast<uintptr_t> (
                              static_cast<uint32_t> (stack[idx - 2])) << 32) |
                              static_cast<uint32_t> (stack[idx - 1]);
      SharedStack *ss = reinterpret_cast<SharedStack *> (ptr);

      ts = ss->stamp;

      // If there is a newer event belonging to another witness,
      // this event has to wait.
      if (!extend_heap.empty () &&
          ts < priority[extend_heap.top ()])
        break;

      extend_shared_stack (ss, uwit, stats);
      stats.events++;
      idx -= 5;
    } else {
      uint32_t p = idx - 1; // p points to the last literal
      assert (stack[p]);
      bool satisfied = false;

      while (stack[p]) {
        const int elit = stack[p];
        if (!satisfied && ival (elit) == elit)
          satisfied = true;
        --p;
      }
      assert (p >= 4); // p is on 0 after the id parts (before the literals)

      ts = static_cast<uint32_t> (stack[p - 3]); 

      if (!extend_heap.empty () &&
          ts < priority[extend_heap.top ()])
        break;

      if (!satisfied) {
        const int sign = (int) (uwit & 1);
        const int ewit = ((int) (uwit >> 1) + 1 ^ -sign) + sign;
        LOG ("ewit %d computed from uwit %u", ewit, uwit);
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
      stats.events++;
      idx = p - 4;
    }                   
  }
  ws_index[uwit] = idx;
  if (idx) {
    priority[uwit] = ts;
    extend_heap.push (uwit);
#ifndef QUIET
      stats.pushed++;
#endif
  }
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
  assert (priority.empty ());
  
  ExtendHeap extend_heap {
    PriorityGreater (priority)
  };

  ws_index.resize (witness_stacks2.size ());
  priority.resize (witness_stacks2.size ());

  for (unsigned uwit = 0; uwit < witness_stacks2.size (); uwit++) {
    WitnessStack &stack = witness_stacks2[uwit];
    if (stack.empty ())
      continue;
#ifndef QUIET
    stats.extension_size += stack.size () - 2;
#endif
    const uint32_t stack_size = stack.size () - 2; // ignore size & capacity
    ws_index[uwit] = stack_size;
    const uint32_t ts = r_timestamp_c (stack.end ());
    assert (ts);

    priority[uwit] = ts;
    extend_heap.push (uwit);
    stats.pushed++;
  }
  
  while (!extend_heap.empty ()) {
    const unsigned uwit = extend_heap.top ();
    extend_heap.pop ();
    LOG ("popped %u (unsigned) from heap", uwit);
    extend_next_c (uwit, extend_heap, stats);
  }

  ws_index.clear ();
  priority.clear ();

  internal->stats.extension_events += stats.events;
  internal->stats.extension_heap_pushed += stats.pushed;
  PHASE ("extend", internal->stats.extensions,
         "extended through extension stack of size %lld", stats.extension_size);
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", stats.flipped);
  extended = true;
  LOG ("extended");
}

/*
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
  assert (priority.empty ());
  
  ExtendHeap extend_heap {
    PriorityGreater (priority)
  };

  ws_index.resize (witness_stacks.size ());
  priority.resize (witness_stacks.size ());

  for (unsigned uwit = 0; uwit < witness_stacks.size (); uwit++) {
    vector<int> &stack = witness_stacks[uwit];
#ifndef QUIET
    stats.extension_size += stack.size ();
#endif
    if (stack.empty ())
      continue;
    uint32_t idx = stack.size ();
    ws_index[uwit] = idx;
    const uint32_t ts = r_timestamp (stack, idx);
    assert (ts);

    priority[uwit] = ts;
    extend_heap.push (uwit);
    stats.pushed++;
  }

  while (!extend_heap.empty ()) {
    const unsigned uwit = extend_heap.top ();
    extend_heap.pop ();
    LOG ("popped %u (unsigned) from heap", uwit);
    extend_next (uwit, extend_heap, stats);
  }

  ws_index.clear ();
  priority.clear ();

  // TODO: add stats and commit extend stats here
  internal->stats.extension_events += stats.events;
  internal->stats.extension_heap_pushed += stats.pushed;
  PHASE ("extend", internal->stats.extensions,
         "extended through extension stack of size %lld", stats.extension_size);
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", stats.flipped);
  extended = true;
  LOG ("extended");
}
*/
bool External::traverse_shared_stack_backward (WitnessIterator &it, SharedStack *ss, unsigned uwit) {
  vector<int> &witness_cube = ss->witness_cube;
  if (witness_cube.empty ()) // stale shared stack. Skip it.
    return true;
  for (const auto &ewit : witness_cube) {
    const unsigned other_uwit = elit2ulit (ewit);
    if (other_uwit != uwit && priority[other_uwit] <= ss->stamp)
      return true;
  }
  vector<int> clause;
  auto p = ss->clause_data.end ();
  auto begin = ss->clause_data.begin ();
  while (p != begin) {
    clause.clear ();
    while (*--p)
      clause.push_back (*p);
    // p points to the 0 before the literals
    const int64_t id = ((int64_t) *(p - 2) << 32) +
                      static_cast<int64_t> (*(p - 1));
    assert (id);
    reverse (clause.begin (), clause.end ());
    if (!it.witness (clause, ss->witness_cube, id))
      return false;
    p -= 4;
  }
  return true;
}

bool External::traverse_shared_stack_forward (WitnessIterator &it, SharedStack *ss, unsigned uwit) {
  vector<int> &witness_cube = ss->witness_cube;
  if (witness_cube.empty ()) // stale shared stack. Skip it.
    return true;
  for (const auto &ewit : witness_cube) {
    const unsigned other_uwit = elit2ulit (ewit);
    if (other_uwit != uwit && priority[other_uwit] >= ss->stamp)
      return true;
  }
  vector<int> clause;
  auto p = ss->clause_data.begin ();
  auto end = ss->clause_data.end ();
  while (p != end) {
    clause.clear ();
    // p points to the first 0: 0 ts idu idl 0 
    const int64_t id = ((int64_t) *(p + 2) << 32) +
                      static_cast<int64_t> (*(p + 3));
    assert (id);
    p += 4; // now is on the 0 before the literals 
    while (*++p)
      clause.push_back (*p);
    // p points to the leading zero of the next clause
    if (!it.witness (clause, ss->witness_cube, id))
      return false;
  }
  return true;
}

// NEW VERSION // _c
bool External::traverse_witnesses_backward (WitnessIterator &it) {
  assert (ws_index.empty ());
  assert (priority.empty ());
  if (internal->unsat)
    return true;
  vector<int> clause, witness;

  ExtendHeap traverse_heap {
    PriorityGreater (priority)
  };

  ws_index.resize (witness_stacks2.size ());
  priority.resize (witness_stacks2.size ());

  for (unsigned uwit = 0; uwit < witness_stacks2.size (); uwit ++) {
    WitnessStack &stack = witness_stacks2[uwit];
    if (stack.empty ())
      continue;
    auto p = stack.end ();
    ws_index[uwit] = p - stack.begin ();
    const uint32_t ts = r_timestamp_c (p);
    assert (ts);
    priority[uwit] = ts;
    traverse_heap.push (uwit);
  }

  while (!traverse_heap.empty ()) {
    const unsigned uwit = traverse_heap.top ();
    traverse_heap.pop ();
    WitnessStack &stack = witness_stacks2[uwit];
    auto p = stack.begin () + ws_index[uwit];
    uint32_t ts = 0;
    while (p != stack.begin ()) {
      // TODO: shared ref handling
      ts = r_timestamp_c (p);
      if (!traverse_heap.empty () &&
          ts < priority[traverse_heap.top ()])
          break;

      p--; // p points to the trailing size field
      bool wit_embedded, id_long;
      unsigned other_lits_size;
      decode_size_field (p, wit_embedded, id_long, other_lits_size);
      
      witness.clear ();
      const int sign = (int) (uwit & 1);
      const int ewit = ((int) (uwit >> 1) + 1 ^ -sign) + sign;
      witness.push_back (ewit);

      p--; // p points to the last literal of the clause
      auto idl_p = p - other_lits_size;
      clause.clear ();
      while (p != idl_p) {
        clause.push_back (*p);
        --p;
      }
      if (wit_embedded)
        clause.push_back (ewit);
      // p points to idl
      int64_t id;
      if (id_long) {
        const uint64_t upper = static_cast<uint32_t> (*(p - 1));
        const uint64_t lower = static_cast<uint32_t> (*p);
        id = static_cast<int64_t> ((upper << 32) | lower);
        p -= 3;
      } else {
        id = static_cast<uint32_t> (*p);
        p -= 2;
      }
      assert (id);
      // p now points to the first size field.
      
      reverse (clause.begin (), clause.end ());

      if (!it.witness (clause, witness, id)) {
        ws_index.clear ();
        priority.clear ();
        return false;
      }
    }
    ws_index[uwit] = p - stack.begin ();

    if (p != stack.begin ()) {
      set_priority (uwit, ts);
      traverse_heap.push (uwit);
    } 
  }
  ws_index.clear ();
  priority.clear ();

  return true;
}
/*
bool External::traverse_witnesses_backward (WitnessIterator &it) {
  assert (ws_index.empty ());
  assert (priority.empty ());

  if (internal->unsat)
    return true;
  vector<int> clause, witness;

  ExtendHeap traverse_heap {
    PriorityGreater (priority)
  };

  ws_index.resize (witness_stacks.size ());
  priority.resize (witness_stacks.size ());

  for (unsigned uwit = 0; uwit < witness_stacks.size (); uwit++) {
    vector<int> &stack = witness_stacks[uwit];
    if (stack.empty ())
      continue;
    uint32_t idx = stack.size ();
    ws_index[uwit] = idx;
    const uint32_t ts = r_timestamp (stack, idx);
    assert (ts);

    priority[uwit] = ts;
    traverse_heap.push (uwit);
  }

  while (!traverse_heap.empty ()) {
    const unsigned uwit = traverse_heap.top ();
    traverse_heap.pop ();
    vector<int> &stack = witness_stacks[uwit];
    uint32_t idx = ws_index[uwit];
    uint32_t ts = 0;
    while (idx) {
      assert (idx >= 5);
      const bool shared_ref = !stack[idx - 3] && 
                            !stack[idx - 4] && 
                            !stack[idx - 5]; 
      if (shared_ref) {
        const uintptr_t ptr =  (static_cast<uintptr_t> (
                              static_cast<uint32_t> (stack[idx - 2])) << 32) |
                              static_cast<uint32_t> (stack[idx - 1]);
        SharedStack *ss = reinterpret_cast<SharedStack *> (ptr);

        ts = ss->stamp;

        if (!traverse_heap.empty () &&
            ts < priority[traverse_heap.top ()])
          break;

        if (!traverse_shared_stack_backward (it, ss, uwit)) {
          priority.clear ();
          ws_index.clear ();
          return false;
        }

        idx -= 5;
      } else {
        uint32_t p = idx - 1; // p points to the last literal
        assert (stack[p]);

        clause.clear ();

        while (stack[p]) {
          clause.push_back (stack[p--]);
        }

        ts = static_cast<uint32_t> (stack[p - 3]);

        if (!traverse_heap.empty () &&
            ts < priority[traverse_heap.top ()])
          break;
      
        witness.clear ();
        const int sign = (int) (uwit & 1);
        const int ewit = ((int) (uwit >> 1) + 1 ^ -sign) + sign;
        witness.push_back (ewit);

        // p points to the '0' before the literals
        const int64_t id = ((int64_t) stack[p - 2] << 32) +
                          static_cast<int64_t> (stack[p - 1]);
        
        assert (id);

        idx = p - 4;

        reverse (clause.begin (), clause.end ());

        if (!it.witness (clause, witness, id)) {
          ws_index.clear ();
          priority.clear ();
          return false;
        }
      }                          
    }
    ws_index[uwit] = idx;

    if (idx) {
      set_priority (uwit, ts);
      traverse_heap.push (uwit);
    }
  }
  ws_index.clear ();
  priority.clear ();

  return true;
}
*/
bool External::traverse_witnesses_forward (WitnessIterator &it) {
  assert (ws_index.empty ());
  assert (priority.empty ());

  if (internal->unsat)
    return true;
  
  vector<int> clause, witness;

  RestoreHeap traverse_heap {
    PriorityLess (priority)
  };

  ws_index.resize (witness_stacks.size ());
  priority.resize (witness_stacks.size ());

  for (unsigned uwit = 0; uwit < witness_stacks.size (); uwit++) {
    vector<int> &stack = witness_stacks[uwit];
    if (stack.empty ())
      continue;
    // get the time stamp of the first clause
    const uint32_t ts = timestamp (stack, 0);
    assert (ts);

    priority[uwit] = ts;
    traverse_heap.push (uwit);
  }

  while (!traverse_heap.empty ()) {
    const unsigned uwit = traverse_heap.top ();
    traverse_heap.pop ();
    vector<int> &stack = witness_stacks[uwit];
    uint32_t idx = ws_index[uwit];
    uint32_t ts = 0;
    while (idx != stack.size ()) {
      // idx is on the start of the next clause
      // shared ref = 0 0 0 ptr_u ptr_l
      const bool shared_ref = !stack[idx] &&
                              !stack[idx + 1] &&
                              !stack[idx + 2];
      if (shared_ref) {
        const uintptr_t ptr = (static_cast<uintptr_t> (
                               static_cast<uint32_t> (stack[idx + 3])) << 32) |
                               static_cast<uint32_t> (stack[idx + 4]);
        SharedStack *ss = reinterpret_cast<SharedStack *> (ptr);

        ts = ss->stamp;

        if (!traverse_heap.empty () &&
            ts > priority[traverse_heap.top ()])
          break;

        if (!traverse_shared_stack_forward (it, ss, uwit)) {
          ws_index.clear ();
          priority.clear ();
          return false;
        }

        idx += 5;
      } else { // 0 ts idu idl 0 l1 ... lk
        ts = static_cast<uint32_t> (stack[idx + 1]);
        if (!traverse_heap.empty () &&
            ts > priority[traverse_heap.top ()])
          break;

        const int64_t id = ((int64_t) stack[idx + 2] << 32) +
                            static_cast<int64_t> (stack[idx + 3]);
        assert (id);

        idx += 5; // idx now on first literal

        clause.clear ();
        while (idx != stack.size () && stack[idx])
          clause.push_back (stack[idx++]);
        // idx now on leading 0 of next clause or on end of stack
        witness.clear ();
        const int sign = (int) (uwit & 1);
        const int ewit = ((int) (uwit >> 1) + 1 ^ -sign) + sign;
        witness.push_back (ewit);

        if (!it.witness (clause, witness, id)) {
          ws_index.clear ();
          priority.clear ();
          return false;
        }
      }
    }
    ws_index[uwit] = idx;

    if (idx != stack.size ()) {
      set_priority (uwit, ts);
      traverse_heap.push (uwit);
    }
  }
  ws_index.clear ();
  priority.clear ();

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
