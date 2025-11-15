#include "internal.hpp"

namespace CaDiCaL {

	#define INVALID64 INT64_MAX
	#define INVALID UINT_MAX
	// ---------------------------------------------------------------------------
	constexpr signed char TRUE   = 1 << 0;
	constexpr signed char TARGET = 1 << 1;
	constexpr signed char WORKED = 1 << 2;
	constexpr signed char REASON_ADDED = 1 << 3;

	signed char &Internal::allrpr_mark (int lit, allrpr_proof_clauses &pcs) {
		assert (internal->vlit (lit) < pcs.marks.size ());
		return pcs.marks[internal->vlit (lit)];
	}

	inline bool Internal::is_true (int lit, allrpr_proof_clauses &pcs) {
	 return allrpr_mark (lit, pcs) & TRUE; 
	}

	inline bool Internal::is_false (int lit, allrpr_proof_clauses &pcs) {
	 return allrpr_mark (-lit, pcs) & TRUE; 
	}

	inline bool Internal::is_target (int lit, allrpr_proof_clauses &pcs) {
	 return allrpr_mark (lit, pcs) & TARGET; 
	}

	inline bool Internal::is_worked (int lit, allrpr_proof_clauses &pcs) {
	 return allrpr_mark (lit, pcs) & WORKED; 
	}

	inline bool Internal::is_reason_added (int lit, allrpr_proof_clauses &pcs) {
		return allrpr_mark (lit, pcs) & REASON_ADDED; 
	}

	inline void Internal::set_true (int lit, allrpr_proof_clauses &pcs)   {
	 allrpr_mark (lit, pcs) |= TRUE; 
	}

	inline void Internal::set_false (int lit, allrpr_proof_clauses &pcs)   {
	 allrpr_mark (lit, pcs) &= ~TRUE; 
	}

	inline void Internal::set_target (int lit, allrpr_proof_clauses &pcs) {
	 allrpr_mark (lit, pcs) |= TARGET; 
	}

	inline void Internal::unset_target (int lit, allrpr_proof_clauses &pcs) {
		allrpr_mark (lit, pcs) &= ~TARGET;
	}

	inline void Internal::set_worked (int lit, allrpr_proof_clauses &pcs) { 
		allrpr_mark (lit, pcs) |= WORKED; 
	}

	inline void Internal::set_reason_added (int lit, allrpr_proof_clauses &pcs) {
	 allrpr_mark (lit, pcs) |= REASON_ADDED; 
	}
	// ---------------------------------------------------------------------------

	void Internal::allrpr_init_citten () {
		assert (!citten);
		citten = kitten_init ();
	}

	void Internal::allrpr_reset_citten () {
		if (citten) {
			kitten_release (citten);
			citten = 0;
		}
	}

	void Internal::allrpr_shuffle(vector<int> &vec) {
		LOG (vec ,"shuffling");
		assert (vec.size ());
		Random random;
    const int n = (int) vec.size ();
    for (int i = 0; i < n; ++i) {
    	int j = random.pick_int (0, n - 1);
    	std::swap(vec[i], vec[j]);
    }
    LOG (vec, "post shuffle:");
	}

extern "C" {

	// Callback function for kitten_trace_core. 
	// Stores a clause from the kitten core for LRAT proof construction.
	// Maps original (cadical known) clauses back to cadical ids (including units).
	// Learned clauses won't be given a cadical id until their proof is emitted.
	//
	/*
	static void extract_clause_from_kitten (void *state, unsigned kitten_id, unsigned allrpr_id, bool learned,
									size_t clause_size, const unsigned *elits,
									size_t chain_size, const unsigned *chain) {
		allrpr_proof_clauses *pcs = (allrpr_proof_clauses *) state;
		Internal *internal = pcs->internal;
		std::vector<allrpr_proof_clause> &core = pcs->proof_clauses;
		std::vector<Clause *> &reasons = pcs->reasons;

		allrpr_proof_clause pc;
		pc.kitten_id = kitten_id;
		pc.learned = learned;
		pc.allrpr_id = INVALID;
		pc.cadical_id = INVALID64;

		if (!learned) { // clause exists in cadical
			assert (clause_size);
			assert (!chain_size);
			if (clause_size == 1) { // special handling of units
				int unit = internal->citten2lit (elits[0]);
				pc.cadical_id = internal->unit_id (unit);
				pc.literals.push_back (unit);
			}
			else {
				pc.allrpr_id = allrpr_id;
				pc.cadical_id = reasons[allrpr_id]->id;
				for (const auto &lit : *reasons[allrpr_id]) {
					pc.literals.push_back (lit);
				}	
			}
		}
		else {
			assert (chain_size);
			pc.allrpr_id = INVALID; // id won't be given until LRAT proof is constructed
			pc.cadical_id = INVALID64;
			const unsigned *end = elits + clause_size;
			for (const unsigned *p = elits; p != end; p++) {
				pc.literals.push_back (internal->citten2lit (*p)); // to signed
			}
			for (const unsigned *p = chain + chain_size; p != chain; p--) {
				pc.chain.push_back (*(p - 1)); // revert chain
			}
		}

	#ifdef LOGGING
  	if (learned) {
    	LOG (pc.literals, "traced learned");
  	}
    else if (pc.literals.size () == 1)
    	LOG (pc.literals, "traced original unit[%lld]", pc.cadical_id);
  	else {
    	assert (pc.allrpr_id < reasons.size ());
    	LOG (reasons[allrpr_id], "traced%s", pcs->is_extra[pc.allrpr_id] ? " extra" : ""); // TODO: remove extra stuff later on
  	}
	#endif
  	core.push_back (pc);
	}
	*/

	static void get_final_from_core (void *state, bool learned, 
																	 size_t clause_size, const unsigned *elits) {
		(void) learned;
		allrpr_mini_pcs *mini_pcs = (allrpr_mini_pcs *) state;
		Internal *internal = mini_pcs->internal;
		std::vector<int> &final = mini_pcs->final_clause;
		// In some weird situations the failing clause already exists in cadical
		final.clear ();
		const unsigned *end = elits + clause_size;
		for (const unsigned *p = elits; p != end; p++) {
			const int lit = internal->citten2lit (*p);
			final.push_back (lit);
		}
	#ifdef LOGGING
		LOG (final, "failing clause");
	#endif
	}
	
} // end extern "C"
	
	
	inline void Internal::feed_reason (allrpr_proof_clauses &pcs, Clause *reason) {
		LOG (reason, "Adding reason");
		const unsigned id = pcs.reasons.size();
		citten_clause_with_id (citten, id, reason->size, reason->literals);
		pcs.reasons.push_back	(reason);
	}

	inline void Internal::feed_unit_reason (int unit) {
		//int64_t id = unit_id (unit);
		//assert (unit_id (unit));
		LOG ("Adding unit clause[%lld] %d", -1, unit);
		citten_clause_with_id (citten, 0, 1, &unit);
	}

	bool Internal::clause_is_qualified (Clause *c, int &prop_lit, allrpr_proof_clauses &pcs) {
		LOG (c, "Checking qualification of");
		assert (!prop_lit);
		if (c->garbage) {
			LOG (c, "Not qualified garbage");
			return false;
		}
		if (c == conflict) {
			LOG (c, "Not qualified conflict");
			return false;
		}

		// A clause would propagate, if it only non-false literal has the highest
		// trail position among literals in the clause
		for (const int &lit : *c) {
			LOG ("checking lit %d", lit);
			if (is_false (lit, pcs)) { // literal is falsified and (in the implication graph or implied)
				LOG ("lit %d falsity implied", lit);
				LOG ("lit %d marks %d", lit, allrpr_mark (lit, pcs));
				LOG ("lit %d marks %d", -lit, allrpr_mark (-lit, pcs));
				continue;
			}
			if (prop_lit) {
				LOG ("Not qualified due to %d being the second non-marked/non-false literal", -lit);
				return false;
			}
			prop_lit = lit; // This may propagate, if it is the only non-false literal
		}
		if (!prop_lit) { // c may be completely falsified
			LOG ("Qualified as possible conflict");
			return true;
		}
		return true;
	}

	// try to collect all necessary reasons and propagating literals without using the flags
	void Internal::allrpr_mark_graph (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR MARK GRAPH V2");
		START (allrprcollect);

		// mark all conflict clause literals negations as true
		LOG ("Setting negated conflict clause literals to true");
		for (const int &lit : *conflict) {
			set_true (-lit, pcs);
			base.push_back (-lit);
		}
		// mark all learned clause literals negations as target
		LOG ("Setting negated learend clause literals as target");
		int work = (int) clause.size ();
		for (const int &lit : clause) {
			set_target (-lit, pcs);
		}
		const auto &t = &trail;
		int i = t->size ();	
		while (work != 0) {
			int lit = (*t)[--i];
			if (!is_true (lit, pcs)) {
				LOG ("skipping non-marked literal %d", lit);
				continue;
			}
			if (is_target (lit, pcs)) {
				LOG ("skipping target literal %d", lit);
				work--;
				continue;
			}
			Var &v = var (lit);
			Clause *reason = v.reason;
			if (!reason)
				continue;
			LOG (reason, "looking at %d reason", lit);
			for (const int &rlit : *reason) {
				if (rlit == lit) // propagating literal
					continue;
				if (is_target (-rlit, pcs) && !is_true (-rlit, pcs)) { // hit a end of the graph
					LOG ("reached learned clause literal %d", rlit);
				}
				if (!is_true (-rlit, pcs)) {
					LOG ("marking %d as true", -rlit);
					set_true (-rlit, pcs); // falsified literal, propagating lit
					base.push_back (-rlit);			
				}
			}
		}
		LOG (base, "base:");
		STOP (allrprcollect);
	}


	void Internal::allrpr_collect_more (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR COLLECT MORE");
		START (allrprcollect);
		vector<int> work;
		int64_t collected = 0;
		// init work stack in order of assumption

		LOG (conflict, "Adding conflict");
		feed_reason (pcs, conflict);
		pcs.is_extra.push_back (0);  // TODO: remove later on
		collected++;
		// add base reasons and queue them up for work
		LOG (base, "Adding base reasons for");
		for (const int &lit : base) {
			Var &v = var (lit);
			if (!v.level) {
				collected++;
				feed_unit_reason (lit);
				set_reason_added (lit, pcs);
			} else if (v.reason) {
				collected++;
				feed_reason (pcs, v.reason);
				set_reason_added (lit, pcs);
				pcs.is_extra.push_back (0);
			} else {
				LOG ("No reason for %d", lit);
			}
			work.push_back (lit);
			set_worked (lit, pcs);
		}

		LOG (work, "initialized work to");
		// Now start at the end of work and look for further propagations given
		// the valuations by the marks. If a literal could propagate, we push it 
		// onto work and mark it.
		while (!work.empty ()) {
			int lit = work.back ();
			assert (is_worked (lit, pcs));
			work.pop_back ();
			LOG ("working on %d", lit);

			LOG ("Checking watch list of %d", -lit);
			Watches &ws = watches (-lit);
			const const_watch_iterator eow = ws.end ();
			watch_iterator j = ws.begin ();

			while (j != eow) {
				const Watch w = *j++;
				int prop_lit = 0;
				if (clause_is_qualified (w.clause, prop_lit, pcs)) {
					if (!prop_lit) {
						LOG (w.clause, "Adding possibly conflict");
						feed_reason (pcs, w.clause);
						pcs.is_extra.push_back (1);
						collected++;
						continue;
					} 
					else {
						Var &vnf = var (prop_lit);
						if (vnf.reason != w.clause) {
							LOG (w.clause, "Adding possibly propagating %d", prop_lit);
							feed_reason (pcs, w.clause);
							pcs.is_extra.push_back (1);
							collected++;
						} 
						else if (!is_reason_added (prop_lit, pcs)) {
							LOG (w.clause, "Adding reason for possibly propagating %d", prop_lit);
							set_reason_added (prop_lit, pcs);
						}
						else {
							LOG (vnf.reason, "Skipping %d reason", prop_lit);
						}
						// Mark and push to work, if wasn't work already
						if (!is_true (prop_lit, pcs)) {
							LOG ("%d is not set to true. setting true flag...", prop_lit);
							set_true (prop_lit, pcs);
						}
						// if the watch list of the literal wasn't yet traversed queue it up for work
						if (!is_worked (prop_lit, pcs)) {
							LOG ("%d wasn't in work yet. pushing to work...", prop_lit);
							work.push_back (prop_lit);
							set_worked (prop_lit, pcs);
						}
					} 
				}
			}
		}
		LOG ("ALLRPR COLLECT MORE FINISHED COLLECTING %lld clauses", collected);
		//LOG (ids, "collected: ");
		stats.allrpr.added += collected;
		STOP (allrprcollect);
	}

	
	void Internal::allrpr_build_lrat (allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR BUILD LRAT");
		START (allrprlrat);
		std::vector<allrpr_proof_clause> &core = pcs.proof_clauses;
		allrpr_proof_clause &final_clause = core[core.size() - 1];

		// found weird trace where the learned clause already existed
		// here the chain is just the existing clauses id
		if (!final_clause.learned) { 
			LOG (final_clause.literals, "deriving LRAT proof for");
			lrat_chain.push_back (final_clause.cadical_id);
			LOG (lrat_chain, "LRAT chain:");
			return;
		}

		unsigned last_learned_id = final_clause.kitten_id;
		int nlearned = 0;
		int norig = 0;
		int extraincore = 0;
		int extragrbinary = 0;
		int extragrternary = 0;
		for (auto &pc: core) {
			if (!pc.learned) { // allready proven clause (known to cadical)
				norig++;
				// TODO: vvv remove later on vvv----------------------------------------
				if (pc.literals.size () == 1) // units are not stored in pcs.reasons
					continue;
				bool is_extra = pcs.is_extra[pc.allrpr_id];
				if (is_extra) {
					if (pc.literals.size () > 2)
						extragrbinary++;
					if (pc.literals.size () > 3)
						extragrternary++;
					extraincore++;
				}
				continue;
			} 
			nlearned++;
			LOG (pc.literals, "deriving LRAT proof for ");
			assert (pc.cadical_id == INVALID64);
			// build chain of cadical ids
			for (auto &kitten_id : pc.chain) {
				int64_t id = 0;
				for (const auto &cpc : core) { // find corresponding clause with kitten_id
					if (cpc.kitten_id != kitten_id)
						continue;
					// found clause with this kitten_id
					id = cpc.cadical_id; // this clause cpc must already be proven or known to cadical
					break;
				}
				assert (id);
				lrat_chain.push_back (id);
			}
			LOG (lrat_chain, "LRAT CHAIN: ");
			// done building chain. Now emit proof line, but only for intermediate 
			// learned clauses. The final learned clause is derived in analyze
			if (proof && pc.kitten_id != last_learned_id) {
				pc.cadical_id = ++clause_id; // get the next free cadical clause id
				proof->add_derived_clause (pc.cadical_id, true, pc.literals, lrat_chain);
				lrat_chain.clear ();
			}
		}
		assert (nlearned > 0);
		if (nlearned - 1) { // only track intermediate clauses.
			LOG ("%d intermediate clauses learned", nlearned - 1);
			stats.allrpr.nintermediate++;
			stats.allrpr.sintermediate += nlearned - 1; 
		}
		stats.allrpr.ncoreclauses += nlearned + norig;
		if (extraincore) {
			stats.allrpr.extraisincore++; // core contains an extra (non-reason) clause
			stats.allrpr.extracsincore += extraincore; // number of extra clauses in core
			if (extragrbinary) {
				stats.allrpr.extragrbinaryincore++;
				stats.allrpr.extragrbinary += extragrbinary;
			}
			if (extragrternary) { // extra clause with size > 3 in core
				stats.allrpr.extragrternaryincore++;
				stats.allrpr.extragrternary += extragrternary;
			}
		}
		// now all intermediate learned clauses are proven.
		STOP (allrprlrat);
	}

	void Internal::allrpr_delete_intermediate_lrat (allrpr_proof_clauses &pcs) {
		START (allrprlrat);
		LOG ("ALLRPR DELETE INTERMEDIATE LRAT");
		// skip last learned clause, which is stored at the end of proof_clauses
		for (size_t i = 0; i < pcs.proof_clauses.size () - 1; i++) {
			allrpr_proof_clause &pc = pcs.proof_clauses[i];
			if (!pc.learned)
				continue;
			LOG ("Deleting clause[%lld]", pc.cadical_id);
			proof->delete_clause (pc.cadical_id, true, pc.literals);
		}
		LOG ("ALLRPR DELETE INTERMEDIATE LRAT FINISHED");
		STOP (allrprlrat);
	} 


	// Reconstructs a LRAT chain for the learned clause in internal->clause.
	// 
	void Internal::allrpr_kitten_catch_rat (int &uip, allrpr_mini_pcs &mini_pcs) {
		START (allrprsolve);
		assert (citten);
	
		// Kitten is now fed with enough clauses.
		// We just need to assume the negation of the learned clause.
		// Some of the assumptions should then fail resulting in a proof of clause
		LOG (clause, "LEARNED CLAUSE: ");
		for (const auto &lit: clause) {
      LOG ("KITTEN ASSUME %d", -lit);
      kitten_assume_signed (citten, -lit);
    }
    
    //#ifdef LOGGING
  	//if (opts.log)
  	//	kitten_set_logging (citten);
  	//#endif
    if (opts.allrprshufflea && !opts.allrprorder && !opts.allrprreverse) {
    	kitten_shuffle_assumptions (citten);
    }
        
    if (opts.allrprshufflec) {
    	kitten_shuffle_clauses (citten);
    }

		kitten_track_antecedents (citten);
		kitten_solve (citten);

		// Now compute the clausal core and trace it. This will provide resolution
		// chains, which can be used for deriving an LRAT proof.
		mini_pcs.cadi_core_clauses = kitten_compute_clausal_core (citten, &mini_pcs.kitten_core_clauses);
		kitten_traverse_core_clauses (citten, &mini_pcs, get_final_from_core);
		stats.allrpr.kittencalls++;
		STOP (allrprsolve);
	}

}	