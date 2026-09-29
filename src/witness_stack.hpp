#ifndef _witness_stack_hpp_INCLUDED
#define _witness_stack_hpp_INCLUDED
namespace CaDiCaL {

// Dynamic array for weakened clauses with a given witness. 
// The stack just consists of a int*. Size and capacity are stored in the 
// first two places of the array. 
//
struct WitnessStack {
	int *stack = nullptr;

	unsigned size () const {
		return stack ? static_cast<unsigned> (stack[0]) : 0;
	}

	unsigned capacity () const {
		return stack ? static_cast<unsigned> (stack[1]) : 0;
	}

	bool empty () const {
		return size () == 0;
	}

	void push_back (int val) {
		if (!stack) { // empty stack <-> nullptr
			allocate (16); // common case
		} else if (stack[0] == stack[1]) { // stack is full. Grow...
			grow ();
		}
		const unsigned size = stack[0]; // old size (also idx to end)
		stack[size] = val; // store value at end of stack
		stack[0] = size + 1; // increment size
	}

	void grow () {
		const unsigned new_cap = 2 * stack[1];
		int *new_stack = new int[new_cap];

		memcpy (new_stack, stack, stack[0] * sizeof (int));
		new_stack[1] = new_cap;

		delete[] stack;
		stack = new_stack;
	}

	void truncate (unsigned new_size) {
		assert (stack);
		assert (new_size >= 2);
		assert (new_size <= static_cast<unsigned> (stack[0]));

		if (new_size == 2) {
			clear ();
			return;
		}
		stack[0] = new_size;
	}

	void shrink_to_fit () {
		if (!stack || stack[0] == stack[1])
			return;

		const unsigned size = stack[0];
		int *new_stack = new int[size];

		memcpy (new_stack, stack, size * sizeof (int));

		new_stack[1] = size;

		delete[] stack;
		stack = new_stack;
	}

	void clear () {
		delete[] stack;
		stack = nullptr;
	}

	void allocate (unsigned capacity) {
		stack = new int[capacity];
		stack[0] = 2;
		stack[1] = capacity;
	}

	int *begin () {
	    return stack ? stack + 2 : nullptr;
	}

	const int *begin () const {
	    return stack ? stack + 2 : nullptr;
	}

	int *end () {
	    return stack ? stack + stack[0] : nullptr;
	}

	const int *end () const {
	    return stack ? stack + stack[0] : nullptr;
	}

	int &operator[] (uint32_t i) {
		assert (stack);
		assert (i < size () - 2);
		return stack[i + 2]; // skip size and capacity
	}

	const int &operator[] (uint32_t i) const {
		assert (stack);
		assert (i < size () - 2);
		return stack[i + 2];
	}
};

} // namespace CaDiCaL
#endif