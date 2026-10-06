#include "internal.hpp"
#include "util.hpp"

namespace CaDiCaL {

void External::push_zero_on_extension_stack () {
  extension.push_back (0);
  LOG ("pushing 0 on extension stack");
}

void External::push_id_on_extension_stack (int64_t id) {
  const uint32_t higher_bits = static_cast<int> (id << 32);
  const uint32_t lower_bits = (id & (((int64_t) 1 << 32) - 1));
  extension.push_back (higher_bits);
  extension.push_back (lower_bits);
  LOG ("pushing id %" PRIu64 " = %d + %d", id, higher_bits, lower_bits);
}

void External::push_clause_literal_on_extension_stack (int ilit) {
  assert (ilit);
  const int elit = internal->externalize (ilit);
  assert (elit);
  extension.push_back (elit);
  LOG ("pushing clause literal %d on extension stack (internal %d)", elit,
       ilit);
}

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

// The extension stack allows to reconstruct a satisfying assignment for the
// original formula after removing eliminated clauses.  This was pioneered
// by Niklas Soerensson in MiniSAT and for instance is described in our
// inprocessing paper, published at IJCAR'12.  This first function adds a
// clause to this stack.  First the blocking or eliminated literal is added,
// and then the rest of the clause.

void External::push_clause_on_extension_stack (Clause *c) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;
  push_zero_on_extension_stack ();
  push_id_on_extension_stack (c->id);
  push_zero_on_extension_stack ();
  for (const auto &lit : *c)
    push_clause_literal_on_extension_stack (lit);
}

void External::push_clause_on_extension_stack_c (Clause *c, int pivot) {
  push_zero_on_extension_stack ();
  push_witness_literal_on_extension_stack (pivot);
  push_clause_on_extension_stack (c);
}

void External::push_binary_clause_on_extension_stack_c (int64_t id, int pivot,
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
/*------------------------------------------------------------------------*/
static constexpr uint32_t CLAUSE_SMALL = 1u << 31;
static constexpr uint32_t EMBEDDED = 1u << 30;
static constexpr uint32_t ID_LONG = 1u << 29;
static constexpr uint32_t SIZE_MASK = (1u << 29) - 1;

// NEW VERSION
// es (idu) idl wit l1 .. lk es
void External::push_clause_on_extension_stack (Clause *c, int pivot) {
  assert (pivot);
  internal->stats.weakened++;
  internal->stats.weakened_lengths += c->size;

  const int ewit = internal->externalize (pivot);
  assert (ewit);
  extension.push_back (0);
  const size_t first_size_field = extension.size () - 1;

  const unsigned size = c->size;
  const bool compactable = size < (1u << 29);
  const bool id_long = c->id > UINT32_MAX; // does not fit into 32 bit

  const uint32_t idu = static_cast<uint32_t> (c->id >> 32);
  const uint32_t idl = static_cast<uint32_t> (c->id);
  if (!compactable || id_long) {
    extension.push_back (static_cast<int> (idu));
    extension.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    extension.push_back (static_cast<int> (idl));
  }
  extension.push_back (ewit);
  bool embedded = false;
  for (const auto &ilit : *c) {
    const int elit = internal->externalize (ilit);
    if (elit == ewit && compactable) {
      embedded = true;
      continue;
    }
    LOG ("pushing clause literal %d on extension stack (internal %d)", elit,
       ilit);
    extension.push_back (elit);
  }

  uint32_t updated_size = c->size;
  if (embedded) {
    updated_size--;
    updated_size |= EMBEDDED;
  }
  if (compactable) {
    updated_size |= CLAUSE_SMALL;
    if (id_long)
      updated_size |= ID_LONG;
  }
  extension[first_size_field] = static_cast<int> (updated_size);
  extension.push_back (static_cast<int> (updated_size));
  if (!marked (witness, ewit))
    mark (witness, ewit);
}

// NEW VERSION
// es (idu) idl wit l_o es
void External::push_binary_clause_on_extension_stack (int64_t id, 
                                                        int pivot, int other) {
  internal->stats.weakened++;
  internal->stats.weakened_lengths += 2;

  const int ewit = internal->externalize (pivot);
  assert (ewit);

  const bool id_long = id > UINT32_MAX; // does not fit into 32 bit
  
  uint32_t encoded_size = 1;
  encoded_size |= EMBEDDED;
  encoded_size |= CLAUSE_SMALL;
  if (id_long)
    encoded_size |= ID_LONG;

  extension.push_back (encoded_size);

  const uint32_t idu = static_cast<uint32_t> (id >> 32);
  const uint32_t idl = static_cast<uint32_t> (id);
  if (id_long) {
    extension.push_back (static_cast<int> (idu));
    extension.push_back (static_cast<int> (idl));
  } else {
    assert (!idu);
    extension.push_back (static_cast<int> (idl));
  }

  extension.push_back (ewit);
  const int elit = internal->externalize (other);
  extension.push_back (elit);
  extension.push_back (encoded_size);
}

inline void decode_size_field (vector<int>::const_iterator size_field, bool &wit_embedded, 
                               bool &id_long, unsigned &other_lits_size) {
  assert (*size_field);

  const uint32_t encoded = static_cast<uint32_t> (*size_field);
  const bool clause_small = encoded & CLAUSE_SMALL;

  wit_embedded = clause_small && (encoded & EMBEDDED);
  id_long = !clause_small || (encoded & ID_LONG);
  other_lits_size = clause_small ? (encoded & SIZE_MASK) : encoded;
}

// NEW VERSION
void External::extend () {
  assert (!extended);
  PROFILE_SCOPE (extend);
  internal->stats.extensions++;

  PHASE ("extend", internal->stats.extensions,
         "mapping internal %d assignments to %d assignments",
         internal->max_var, max_var);

#ifndef QUIET
  int64_t updated = 0;
#endif
  for (unsigned i = 1; i <= (unsigned) max_var; i++) {
    const int ilit = e2i.find (i).second;
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
    i--; // i points to the trailing size field of the next clause
    // es (idu) idl wit l1 .. lk es

    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (i, wit_embedded, id_long, other_lits_size);

    i--; // i points to the last literal of the clause

    bool satisfied = false;
    auto end_of_lits = i - other_lits_size;
    while (i != end_of_lits) {
      if (satisfied) {
        --i;
        continue;
      }
      if (ival (*i) == *i)
        satisfied = true;
      assert (i != begin);
      --i;
    }

    // i now points to the witness. 
    if (wit_embedded) 
      if (!satisfied && ival (*i) == *i)
        satisfied = true;

    if (!satisfied) {
      const int lit = *i;
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
    // move i to the first size field of the extended clause
    i -= (id_long ? 3 : 2); 
  }
  PHASE ("extend", internal->stats.extensions,
         "flipped %" PRId64 " literals during extension", flipped);
  extended = true;
  LOG ("extended");
}

/*------------------------------------------------------------------------*/
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
    int ilit = e2i.find_or_default (eidx, 0);
    if (!ilit) {
      init (eidx);
      assert (e2i.find_or_default (eidx, 0));
      ilit = e2i.find (eidx).second;
    }
    assert (ilit && ilit != INT_MIN);
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
    int ilit = e2i.find_or_default (eidx, 0);
    if (!ilit) {
      init (eidx);
      assert (e2i.find_or_default (eidx, 0));
      ilit = e2i.find (eidx).second;
    }
    assert (ilit && ilit != INT_MIN);
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

void External::extend_c () {

  assert (!extended);
  PROFILE_SCOPE (extend);
  internal->stats.extensions++;

  PHASE ("extend", internal->stats.extensions,
         "mapping internal %d assignments to %d assignments",
         internal->max_var, max_var);

#ifndef QUIET
  int64_t updated = 0;
#endif
  for (unsigned i = 1; i <= (unsigned) max_var; i++) {
    const int ilit = e2i.find (i).second;
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
}

/*------------------------------------------------------------------------*/
// NEW VERSION
bool External::traverse_witnesses_backward_c (WitnessIterator &it) {
  if (internal->unsat)
    return true;

  vector<int> clause, witness;

  const auto begin = extension.begin ();
  auto p = extension.end ();

  while (p != begin) {
    --p;
    bool wit_embedded, id_long;
    unsigned other_lits_size;
    decode_size_field (p, wit_embedded, id_long, other_lits_size);

    auto q = p - 1;
    auto wit = q - other_lits_size;

    clause.clear ();
    while (q != wit)
      clause.push_back (*q--);
    
    if (wit_embedded)
      clause.push_back (*wit);

    witness.clear ();
    witness.push_back (*wit);

    int64_t id;

    if (id_long) {
      const uint64_t lower = static_cast<uint32_t> (*(wit - 1));
      const uint64_t upper = static_cast<uint32_t> (*(wit - 2));
      id = static_cast<int64_t> ((upper << 32) | lower);
      p = wit - 3;             // points to initial size field
    } else {
      id = static_cast<uint32_t> (*(wit - 1));
      p = wit - 2;             // points to initial size field
    }

    assert (id);

    reverse (clause.begin (), clause.end ());

    LOG (clause, "traversing clause");

    if (!it.witness (clause, witness, id))
      return false;
  }

  return true;
}

// NEW VERSION
bool External::traverse_witnesses_forward_c (WitnessIterator &it) {
  if (internal->unsat)
    return true;

  vector<int> clause, witness;

  const auto end = extension.end ();
  auto p = extension.begin ();

  while (p != end) {
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

    assert (id);

    auto wit = p + (id_long ? 3 : 2);
    auto begin_of_lits = wit + 1;
    auto end_of_lits = begin_of_lits + other_lits_size; // trailing size field

    witness.clear ();
    witness.push_back (*wit);

    clause.clear ();
    for (auto q = begin_of_lits; q != end_of_lits; ++q)
      clause.push_back (*q);
    if (wit_embedded)
      clause.push_back (*wit);
    if (!it.witness (clause, witness, id))
      return false;
    p = end_of_lits + 1;
  }
  return true;
}

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
