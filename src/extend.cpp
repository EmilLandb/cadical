#include "internal.hpp"

namespace CaDiCaL {

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

// Push a clauses id and literals on witness stack x
void External::push_clause_on_extension_stack (int wit, Clause *c) {
  assert (wit);
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;

  const int ewit = internal->externalize (wit);
  assert (ewit);
  
  push_zero_on_extension_stack (ewit);
  push_id_on_extension_stack (ewit, c->id);
  push_zero_on_extension_stack (ewit);
  for (const auto &lit : *c)
    push_clause_literal_on_extension_stack (ewit, lit);
  
  // Now also mark the witness
  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }
  witness_order.push_back (ewit);
}

void External::push_binary_clause_on_extension_stack (int64_t id, int wit,
                                                      int other) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += 2;

  const int ewit = internal->externalize (wit);
  assert (ewit);

  push_zero_on_extension_stack (ewit);
  push_id_on_extension_stack (ewit, id);
  push_zero_on_extension_stack (ewit);
  push_clause_literal_on_extension_stack (ewit, wit);
  push_clause_literal_on_extension_stack (ewit, other);

  // Mark the witness
  if (!marked (witness, ewit)) {
    LOG ("marking as witness %d (external)", ewit);
    mark (witness, ewit);
  }
  witness_order.push_back (ewit);
}

/*------------------------------------------------------------------------*/
vector<int>* External::create_shared_stack (const vector<int> &iwit_cube) {
  assert (!iwit_cube.empty ());
  vector<int> *ss = new vector<int>;
  
  const uintptr_t ptr = reinterpret_cast<uintptr_t> (ss);
  const int upper = static_cast<int> (ptr >> 32);
  const int lower = static_cast<int> (ptr & 0xffffffff);

  // push a reference to all witness stacks of literals in the cube
  for (const auto &iwit : iwit_cube) {
    assert (iwit);
    const int ewit = internal->externalize (iwit);
    assert (ewit);

    ss->push_back (ewit);

    if (!marked (witness, ewit))
      mark (witness, ewit);
  }
  // push a reference to witness_order
  // 0 p_u p_l 0
  witness_order.push_back (0);
  witness_order.push_back (upper);
  witness_order.push_back (lower);
  witness_order.push_back (0);
  LOG (*ss, "shared stack: ");
  return ss;
}

void External::push_shared_clause (vector<int> *ss, Clause *c) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;

  const uint32_t higher_bits = static_cast<int> (c->id >> 32);
  const uint32_t lower_bits = (c->id & (((int64_t) 1 << 32) - 1));
  LOG ("pushing id %" PRIu64 " = %d + %d on shared stack ", 
       c->id, higher_bits, lower_bits);
  
  // 0 id_u id_l 0 l1 l2 .. lk
  ss->push_back (0);
  ss->push_back (higher_bits);
  ss->push_back (lower_bits);
  ss->push_back (0);

  for (const auto &ilit : *c) {
    assert (ilit);
    const int elit = internal->externalize (ilit);
    assert (elit);
    ss->push_back (elit);
  }
  LOG (*ss, "shared stack: ");
}

void External::create_shared_stack_and_push_clause (
    const vector<int> &iwit_cube, Clause *c) {
  LOG (c, "Creating a shared stack for a single clause with witness cube.");
  vector<int> *ss = create_shared_stack (iwit_cube);
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

void External::extend_shared_stack (vector<int> *ss) {
  LOG ("Extending shared stack of size %zu", 
       ss->size ());
  // first check the cube for being satisfied.
  auto p = ss->begin ();
  bool satisfied = true;
  while (*p) {
    const int ewit = *p;
    if (ival (ewit) != ewit) // some witness falsified
      satisfied = false;
    ++p;
  }
  if (satisfied) {
    LOG (ss->begin (), p, 
        "Shared stack clauses are satisfied by the witness cube.");
    return;
  }
  
  // Check for unsatisfied clauses. 
  bool assign_witness = false;
  auto q = ss->end ();
  while (q != p) { // p is on the first '0' of the first clause
    --q;

    assert (*q); // last literal of next clause to check
    bool clause_satisfied = false;
    while (*q) {
      const int elit = *q;
      if (ival (elit) == elit)
        clause_satisfied = true;
      --q;
    }
    if (!clause_satisfied) {
      assign_witness = true;
      break;
    }
    // now comes the id part 0 id_u id_l 0
    //                                   ^
    q -= 3;
  }
  if (assign_witness) {
    assert (!*p); // p should be on '0' after the witness cube
    while (*--p) {
      const int ewit = *p;
      if (ival (ewit) == ewit)
        continue;
      LOG ("flipping witness literal %d", ewit);
      assert (ewit != INT_MIN);
      size_t idx = abs (ewit);
      if (idx >= vals.size ())
        vals.resize (idx + 1, false);
      vals[idx] = !vals[idx];
      internal->stats.extended++;
#ifndef QUIET
      //flipped++;
      // TODO: Introduce extend stats
#endif
    }
  }
}

void External::extend () {
  assert (!extended);
  START (extend);
  internal->stats.extensions++;
  size_t witness_order_size = witness_order.size ();
  if (witness_order_size > internal->stats.extensionmaxwit)
    internal->stats.extensionmaxwit = witness_order_size;

  PHASE ("extend", internal->stats.extensions,
         "mapping internal %d assignments to %d assignments",
         internal->max_var, max_var);
#ifndef QUIET
  int64_t updated = 0;
#endif
  // Copy the internal assignment into an external one
  for (unsigned i = 1; i <= (unsigned) max_var; i++) { 
    const int ilit = e2i[i];
    if (!ilit)
      continue;
    if (i >= vals.size ())
      vals.resize (i + 1, false);
    vals[i] = (internal->val (ilit) > 0);
#ifndef QUIET
    updated++;
#endif
  }
  vector<size_t> ws_index (witness_stacks.size ()); // initialize to size of witness_stacks
  size_t extension_size = 0;
  for (size_t i = 0; i < witness_stacks.size (); i++) {
    LOG (witness_stacks[i], "witness_stacks[%zu] (ulit)", i);
    const size_t stack_size = witness_stacks[i].size ();
    ws_index[i] = stack_size;
    extension_size += stack_size; // TODO: does not account for shared stack sizes
  }

  PHASE ("extend", internal->stats.extensions,
         "updated %" PRId64 " external assignments", updated);
  PHASE ("extend", internal->stats.extensions,
         "extending through extension stack of size %zd",
         extension_size);
#ifndef QUIET
  int64_t flipped = 0;
#endif
  LOG (witness_order, "witness_order: ");
  auto p = witness_order.end ();
  auto begin = witness_order.begin ();
  while (p != begin) {
    p--;
    // p is either on a single witness or a zero which indicates the
    // start of a shared stack reference
    int ewit = *p;
    if (!ewit) { // Shared stack! 
      // 0 id_u id_l 0
      //             ^
      const uintptr_t ptr =
          (static_cast<uintptr_t> (static_cast<uint32_t> (*(p - 2))) << 32) |
           static_cast<uint32_t> (*(p - 1));
      vector<int> *ss = reinterpret_cast<vector<int> *> (ptr);
      extend_shared_stack (ss);
      p -= 3; // Now p is on the 0 after the reference.
    } 
    else { // regular entry (of a single witness clause)
      const unsigned uwit = elit2ulit (ewit);  
      vector<int>& wstack = witness_stacks[uwit];
      LOG (wstack, "witness_stack[%u] (external %d)", uwit, ewit);
      bool satisfied = false;
      if (ival (ewit) == ewit) { // Witness satisfied
        LOG ("witness satisfied.");
        satisfied = true;
      }         
      // Else we need to check the last clause. We skip shared stacks here
      // because they are referenced explicitly in witness_order.
      size_t idx = ws_index[uwit];
      
      if (!idx) {
        ws_index[uwit] = 0;
        continue;
      }
        
      // Check the clauses literals 
      while (wstack[--idx] != 0) { // go to next '0' then should come the id
        LOG ("checking clause literal %d (external)", wstack[idx]);
        if (satisfied)
          continue;
        int elit = wstack[idx];
        // If lit is satisfied we can just skip the clause
        if (ival (elit) == elit) {
          LOG ("satisfied literal %d (external)", elit);
          satisfied = true;
        }
      }
      // now idx should be the index of the '0' before the idu idl part. update.
      assert (idx >= 3);
      ws_index[uwit] = idx - 3; // leave the index directly before the next clause, i.e. on '0'

      // and check whether we need to flip the witness
      if (!satisfied) {
        assert (ival (ewit) != ewit); // Witness should not be assigned
        size_t var = abs (ewit); // Get the variable 
        if (var >= vals.size ()) // Check whether we need to resize vals
          vals.resize (var + 1, false);
        LOG ("assiging ewit %d", ewit);
        vals[var] = !vals[var]; // Set to true
        internal->stats.extended++;
#ifndef QUIET
      flipped++;
#endif
      }
    }
  }
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", flipped);
  extended = true;
  LOG ("extended");
  STOP (extend);
}

/*------------------------------------------------------------------------*/
// TODO: update: we have also shared stacks now...
// For now this only works for single witnessed clauses.
// For witness cube clauses there is still a problem since we have to sweep
// across the ends of all witness stacks to see if there is a shared clause and
// thereby collect all witnesses in the cube.
bool External::traverse_witnesses_backward (WitnessIterator &it) {
  if (internal->unsat)
    return true;
  vector<int> clause, witness;
  //const auto begin = extension.begin (); 
  //auto i = extension.end ();
  vector<size_t> ws_index (witness_stacks.size ()); // initialize to size of witness_stacks
  for (size_t i = 0; i < witness_stacks.size (); i++) {
    const size_t stack_size = witness_stacks[i].size ();
    ws_index[i] = stack_size;
  }
  for (size_t i = witness_order.size (); i-- > 0;) {
    int ewit = witness_order[i];
    const unsigned uwit = elit2ulit (ewit);
    if (ws_index[uwit] == 0) // stale entry
      continue;
    vector<int>& wstack = witness_stacks[uwit];
    size_t idx = ws_index[uwit];
    // get literals of the clause
    assert (idx > 0);
    while (wstack[--idx] != 0) {
      int elit = wstack[idx];
      clause.push_back (elit);
    } 
    witness.push_back (ewit); // and the witness (single witness assumption)
    assert (idx >= 4);
    // now idx should be the index of the '0' before the two id fields
    // so  wstack[idx - 1] is idl
    // and wstack[idx - 2] is idu
    // and wstack[idx - 3] is stamp
    const int64_t id = ((int64_t) wstack[idx - 2] << 32) + 
                       static_cast<int64_t> (wstack[idx - 1]);
    assert (id);
    ws_index[uwit] = idx - 4; // leave the index directly before the next clause
    reverse (clause.begin (), clause.end ());
    //reverse (witness.begin (), witness.end ()); // Need later on for witness cubes
    LOG (clause, "traversing clause");
    if (!it.witness (clause, witness, id))
      return false;
    clause.clear ();
    witness.clear ();
  }
  return true;
}
/*
  bool External::traverse_witnesses_backward (WitnessIterator &it) {
    if (internal->unsat)
      return true;
    vector<int> clause, witness;
    const auto begin = extension.begin ();
    auto i = extension.end ();
    while (i != begin) {
      int lit;
      while ((lit = *--i))
        clause.push_back (lit);
      assert (!lit);
      --i;
      const int64_t id =
          ((int64_t) * (i - 1) << 32) + static_cast<int64_t> (*i);
      assert (id);
      i -= 2;
      assert (!*i);
      assert (i != begin);
      while ((lit = *--i))
        witness.push_back (lit);
      reverse (clause.begin (), clause.end ());
      reverse (witness.begin (), witness.end ());
      LOG (clause, "traversing clause");
      if (!it.witness (clause, witness, id))
        return false;
      clause.clear ();
      witness.clear ();
    }
    return true;
  }
*/

// TODO: Update to work with new data structure
// Here we have a bigger problem currently: We always have a suffix of 
// witness order that is not stale but we only know when an entry is stale 
// while traversing backwards. So this is for now not supported at all.
// We would need to rewrite the witness order stack after every restoration.
bool External::traverse_witnesses_forward (WitnessIterator &it) {
  if (internal->unsat)
    return true;
  vector<int> clause, witness;
  const auto end = extension.end ();
  auto i = extension.begin ();
  if (i != end) {
    int lit = *i++;
    do {
      assert (!lit), (void) lit;
      while ((lit = *i++))
        witness.push_back (lit);
      assert (!lit);
      assert (i != end);
      assert (!*i);
      const int64_t id =
          ((int64_t) *i << 32) + static_cast<int64_t> (*(i + 1));
      assert (id > 0);
      i += 3;
      assert (*i);
      assert (i != end);
      while (i != end && (lit = *i++))
        clause.push_back (lit);
      if (!it.witness (clause, witness, id))
        return false;
      clause.clear ();
      witness.clear ();
    } while (i != end);
  }
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
