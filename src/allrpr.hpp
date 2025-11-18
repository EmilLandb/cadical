#ifndef _allrpr_hpp_INCLUDED
#define _allrpr_hpp_INCLUDED

namespace CaDiCaL {

	struct Internal;

	// exported kitten clause
	struct allrpr_proof_clause {
		unsigned allrpr_id;
		unsigned kitten_id;
		int64_t cadical_id;
		bool learned;
		std::vector<int> literals;
		std::vector<unsigned> chain;
	};

	// we don't need to store unit clauses. Once a non-learned size 1 clause is 
	// returned from kitten, we can get it's id by unit_id (). It is important,
	// that units are not added to reasons.
	struct allrpr_proof_clauses {
		Internal *internal;
		std::vector<struct Clause *> reasons; // indexed by allrpr_id
		std::vector<bool> is_extra;  // TODO: remove later on
		std::vector<allrpr_proof_clause> proof_clauses; // output of kitten
		std::vector<signed char> marks; // own marks for literals
	};


	// For Version without LRAT
	struct allrpr_mini_pcs {
		Internal *internal;
		uint64_t cadi_core_clauses = 0;
		uint64_t kitten_core_clauses = 0;
		std::vector<int> final_clause;
	};

}
#endif