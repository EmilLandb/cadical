#include "internal.hpp"

namespace CaDiCaL {
/*
void External::push_zero_on_extension_stack () {
  extension.push_back (0);
  LOG ("pushing 0 on extension stack");
}
*/
void External::push_zero_on_extension_stack (int ewit) {
  assert (ewit);
  const unsigned uwit = elit2ulit (ewit);
  if (uwit >= witness_stacks.size ())
    witness_stacks.resize (uwit + 1); // the witness bitset is resized in mark
  witness_stacks[uwit].push_back (0);
  LOG ("pushing 0 on witness stack %d (external)", ewit);
}

/*
void External::push_id_on_extension_stack (int64_t id) {
  const uint32_t higher_bits = static_cast<int> (id << 32);
  const uint32_t lower_bits = (id & (((int64_t) 1 << 32) - 1));
  extension.push_back (higher_bits);
  extension.push_back (lower_bits);
  LOG ("pushing id %" PRIu64 " = %d + %d", id, higher_bits, lower_bits);
}
*/

void External::push_id_on_extension_stack (int ewit, int64_t id) {
  assert (ewit);
  const uint32_t higher_bits = static_cast<int> (id >> 32);
  const uint32_t lower_bits = (id & (((int64_t) 1 << 32) - 1));
  const unsigned uwit = elit2ulit (ewit);
  assert (uwit < witness_stacks.size ());
  //if (uwit >= witness_stacks.size ())
  //  witness_stacks.resize (uwit + 1); // the witness bitset is resized in mark
  witness_stacks[uwit].push_back (higher_bits);
  witness_stacks[uwit].push_back (lower_bits);
  LOG ("pushing id %" PRIu64 " = %d + %d on witness stack %d (external)", 
      id, higher_bits, lower_bits, ewit);
}

void External::push_stamp_on_extension_stack (int ewit) {
  assert (ewit);
  const unsigned uwit = elit2ulit (ewit);
  assert (uwit < witness_stacks.size ());
  witness_stacks[uwit].push_back (++stamp);
  LOG ("pushing time stamp %u on witness stack %d (external)", stamp, ewit);
}
/*
void External::push_clause_literal_on_extension_stack (int ilit) {
  assert (ilit);
  const int elit = internal->externalize (ilit);
  assert (elit);
  extension.push_back (elit);
  LOG ("pushing clause literal %d on extension stack (internal %d)", elit,
       ilit);
}
*/

void External::push_clause_literal_on_extension_stack (int ewit, int ilit) {
  assert (ilit);
  assert (ewit);
  const int elit = internal->externalize (ilit);
  assert (elit);
  const unsigned uwit = elit2ulit (ewit);
  assert (uwit < witness_stacks.size ());
  //if (uwit >= witness_stacks.size ())
  //  witness_stacks.resize (uwit + 1); // the witness bitset is resized in mark
  witness_stacks[uwit].push_back (elit);
  LOG ("pushing clause literal %d on witness stack %d (external) (internal %d)", elit, 
       ewit , ilit);
}

/*
void External::push_witness_literal_on_extension_stack (int ilit) {
  assert (ilit);
  const int elit = internal->externalize (ilit);
  assert (elit);
  extension.push_back (elit);
  LOG ("pushing witness literal %d on extension stack (internal %d)", elit,
       ilit);
  if (marked (witness, elit))
    return;
  LOG ("marking witness %d", elit);
  mark (witness, elit);
}
*/

// The extension stack allows to reconstruct a satisfying assignment for the
// original formula after removing eliminated clauses.  This was pioneered
// by Niklas Soerensson in MiniSAT and for instance is described in our
// inprocessing paper, published at IJCAR'12.  This first function adds a
// clause to this stack.  First the blocking or eliminated literal is added,
// and then the rest of the clause.
/*
void External::push_clause_on_extension_stack (Clause *c) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;
  push_zero_on_extension_stack ();
  push_id_on_extension_stack (c->id);
  push_zero_on_extension_stack ();
  for (const auto &lit : *c)
    push_clause_literal_on_extension_stack (lit);
}
*/

// Push a clauses id and literals on witness stack x
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
  if (!marked (witness, ewit))
    mark (witness, ewit);
  witness_order.push_back (ewit);
}

/*
void External::push_clause_on_extension_stack (Clause *c, int pivot) {
  push_zero_on_extension_stack ();
  push_witness_literal_on_extension_stack (pivot);
  push_clause_on_extension_stack (c);
}
*/

/*
void External::push_binary_clause_on_extension_stack (int64_t id, int pivot,
                                                      int other) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += 2;
  push_zero_on_extension_stack ();
  push_witness_literal_on_extension_stack (pivot);
  push_zero_on_extension_stack ();
  push_id_on_extension_stack (id);
  push_zero_on_extension_stack ();
  push_clause_literal_on_extension_stack (pivot);
  push_clause_literal_on_extension_stack (other);
}
*/

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
  if (!marked (witness, ewit))
    mark (witness, ewit);
  witness_order.push_back (ewit);
}

void External::push_shared_clause_on_extension_stack (vector<int> wits, 
                                                      Clause *c) {
  LOG (wits, "pushing shared clause references on witness stacks");
  // create the shared clause
  const size_t bytes = sizeof (SharedClause) + (c->size + 1) * sizeof (int);

  SharedClause *sc = (SharedClause*) new char[bytes];
  DeferDeleteArray<char> shared_delete ((char *) sc);
  sc->id = c->id;
  sc->backlinks = wits.size ();
  sc->force_witness = false;
  sc->stale = false;

  for (int i = 0; i < c->size; ++i) {
    int ilit = c->literals[i];
    sc->elits[i] = internal->externalize (ilit);
  }
  sc->elits[c->size] = 0;
  const uintptr_t ptr = reinterpret_cast<uintptr_t> (sc);
  const uint32_t higher_bits = ptr >> 32;
  const uint32_t lower_bits = ptr & 0xffffffffu;
  // now connect dummy clauses
  for (auto &wit : wits) {
    const int ewit = internal->externalize (wit);
    const unsigned uwit = elit2ulit (ewit);
    
    if (!marked (witness, ewit))
      mark (witness, ewit);
    
    witness_order.push_back (ewit);

    if (uwit >= witness_stacks.size ()) 
      witness_stacks.resize (uwit + 1); // the witness bitset is resized in mark

    witness_stacks[uwit].push_back (0);
    witness_stacks[uwit].push_back (0);
    witness_stacks[uwit].push_back (0);
    witness_stacks[uwit].push_back (higher_bits);
    witness_stacks[uwit].push_back (lower_bits);
  }

  shared_delete.release ();
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
  void External::extend () {

    assert (!extended);
    START (extend);
    internal->stats.extensions++;

    PHASE ("extend", internal->stats.extensions,
           "mapping internal %d assignments to %d assignments",
           internal->max_var, max_var);

  #ifndef QUIET
    int64_t updated = 0;
  #endif
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
    PHASE ("extend", internal->stats.extensions,
           "updated %" PRId64 " external assignments", updated);
    PHASE ("extend", internal->stats.extensions,
           "extending through extension stack of size %zd",
           extension.size ());
    const auto begin = extension.begin ();
    auto i = extension.end ();
  #ifndef QUIET
    int64_t flipped = 0;
  #endif
    while (i != begin) {
      bool satisfied = false;
      int lit;
      assert (i != begin);
      while ((lit = *--i)) {
        if (satisfied)
          continue;
        if (ival (lit) == lit)
          satisfied = true;
        assert (i != begin);
      }
      assert (i != begin);
      LOG ("id=%" PRId64, ((int64_t) *i << 32) + *(i - 1));
      assert (*i || *(i - 1));
      --i;
      assert (i != begin);
      --i;
      assert (i != begin);
      assert (!*i);
      --i;
      assert (i != begin);
      if (satisfied)
        while (*--i)
          assert (i != begin);
      else {
        while ((lit = *--i)) {
          const int tmp = ival (lit); // not 'signed char'!!!
          if (tmp != lit) {
            LOG ("flipping blocking literal %d", lit);
            assert (lit);
            assert (lit != INT_MIN);
            size_t idx = abs (lit);
            if (idx >= vals.size ())
              vals.resize (idx + 1, false);
            vals[idx] = !vals[idx];
            internal->stats.extended++;
  #ifndef QUIET
            flipped++;
  #endif
          }
          assert (i != begin);
        }
      }
    }
    PHASE ("extend", internal->stats.extensions,
           "flipped %" PRId64 " literals during extension", flipped);
    extended = true;
    LOG ("extended");
    STOP (extend);
  }
*/

void External::extend () {
  assert (!extended);
  START (extend);
  internal->stats.extensions++;
  // TODO: Maybe remove stat later.
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
  // TODO: If we keep track of the number of unfinished witness_stacks 
  //       we can stop as soon as we have finished all.
  vector<size_t> ws_index (witness_stacks.size ()); // initialize to size of witness_stacks
  int nstacks = 0; // Number of stacks that still have clauses to process
  size_t extension_size = 0;
  for (size_t i = 0; i < witness_stacks.size (); i++) {
    const size_t stack_size = witness_stacks[i].size ();

    if (stack_size)
      nstacks++;

    ws_index[i] = stack_size;
    extension_size += stack_size;
  }

  PHASE ("extend", internal->stats.extensions,
         "updated %" PRId64 " external assignments", updated);
  PHASE ("extend", internal->stats.extensions,
         "extending through extension stack of size %zd",
         extension_size);
#ifndef QUIET
  int64_t flipped = 0;
#endif

  for (size_t i = witness_order.size (); i-- > 0;) { // points behind last element but we decrement first
    if (!nstacks) { // No more work. Just possibly more entries in witness_order
      LOG ("Finished extending after seeing %zu entries", witness_order_size - i);
      break; // TODO: We could also compact the prefix but i am unsure whether this
             // this early exit is practical at all.
    }
    int ewit = witness_order[i];
    const unsigned uwit = elit2ulit (ewit);
    if (ws_index[uwit] == 0) // the entry is stale. Skip it.
      continue;
    vector<int>& wstack = witness_stacks[uwit];
    LOG (wstack, "witness_stack[%u]", uwit);
    bool satisfied = false;
    if (ival (ewit) == ewit)  // Witness satisfied
      satisfied = true;
    // Else we need to check the last clause of the corresponding witness stack
    size_t idx = ws_index[uwit]; // get the current "end" of the corresp. witness stack
    // Now it is time to parse the next clause and update ws_index
    // The current situation should look something like:
    //  ts idu idl 0 l1 l2 l3 ... lk .
    //                               ^
    //                              idx

    // We look ahead to detect dummy clauses which look like this:
    // 0 0 0 ptr_u ptr_l 
    // This cannot occur for a regular clause so it happens exactly in 
    // the shared clause case.
    const bool shared = !wstack[idx - 3] && 
                        !wstack[idx - 4] && 
                        !wstack[idx - 5];
    if (shared) {
      LOG ("shared clause detected.");
      const uintptr_t ptr = (static_cast<uintptr_t> (wstack[idx - 2]) << 32) |
                             static_cast<uint32_t> (wstack[idx - 1]);

      SharedClause *sc = reinterpret_cast<SharedClause*> (ptr);
      LOG ("id of clause: %lld", sc->id);
      if (sc->stale) {
        LOG ("clause is stale. Skipping...");
        continue;
      }
      // Careful. If ewit is already assigned we would flip it instead
      else if (sc->force_witness && (ival (ewit) != ewit)) { 
        LOG ("Witness is forced since part of a witness cube");
        satisfied = false;
      }
      else {
        LOG ("Checking satisfaction of shared clause");
        for (int *p = sc->elits; *p; ++p) {
          int elit = *p;
          if (ival (elit) == elit) {
            LOG ("clause satisfied by %d (elit)", elit);
            satisfied = true;
            break;
          }
          LOG ("not sat elit %d", elit);
        }
        if (!satisfied) {
          LOG ("clause is not satisfied!");
          sc->force_witness = true;
        }
      }
      assert (idx >= 5);
      ws_index[uwit] = idx - 5; // advance index. 2 pointer parts + 2 zeros
    }
    else {
      while (wstack[--idx] != 0) { // go to next '0' then should come the id
        if (satisfied)
          continue;
        int elit = wstack[idx];
        // If lit is satisfied we can just skip the clause
        if (ival (elit) == elit)
          satisfied = true;
      }
      // now idx should be the index of the '0' before the ts idu idl part. update.
      assert (idx >= 4);
      ws_index[uwit] = idx - 4; // leave the index directly before the next clause, i.e. on '0'
    }
    if (!ws_index[uwit]) { // Stack is processed. No more extensions with the current witness
      LOG ("witness stack of %d is completely processed", ewit);
      nstacks--; 
    }
 
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
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", flipped);
  extended = true;
  LOG ("extended");
  STOP (extend);
}

/*------------------------------------------------------------------------*/
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
