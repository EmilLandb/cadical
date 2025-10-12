//#include "allrpr.hpp"
#include "internal.hpp"

namespace CaDiCaL {

	#define INVALID64 INT64_MAX
	#define INVALID UINT_MAX

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

extern "C" {

	// Callback function for kitten_trace_core. 
	// Stores a clause from the kitten core for LRAT proof construction.
  // Maps original (cadical known) clauses back to cadical ids (including units).
  // Learned clauses won't be given a cadical id until their proof is emitted.
	//
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
  	if (learned)
    	LOG (pc.literals, "traced %s",
         	 pc.learned == true ? "learned" : "original");
    else if (pc.literals.size () == 1)
    	LOG (pc.literals, "traced %s unit[%lld]",
         	 pc.learned == true ? "learned" : "original", pc.cadical_id);
  	else {
    	assert (pc.allrpr_id < reasons.size ());
    	LOG (reasons[allrpr_id], "traced");
  	}
	#endif
  	core.push_back (pc);
	}
} // end extern "C"

	
	inline void Internal::feed_reason (allrpr_proof_clauses &pcs, Clause *reason) {
		const unsigned id = pcs.reasons.size();
		citten_clause_with_id (citten, id, reason->size, reason->literals);
		pcs.reasons.push_back	(reason);
	}

	inline void Internal::feed_unit_reason (int unit) {
		int64_t id = unit_id (unit);
		assert (unit_id (unit));
		citten_clause_with_id (citten, id, 1, &unit);
	}

	// collects reasons necessary for deriving a proof of the learned clause
	// and feeds them to kitten 
	//
	void Internal::allrpr_collect_learn_reasons (int &uip, allrpr_proof_clauses &pcs) {
		START (allrprcollect);
		LOG ("ALLRPR COLLECT LEARNED REASONS");
		assert (conflict);
		assert (citten);
		LOG (conflict, "add conflict clause");
		// add conflict clause. Will finally be falsified by the assumptions
		feed_reason (pcs, conflict);
	
		// Collect necessary clauses by going backwards from the end of the trail
		// up to the uip. Each "seen" assignments reason is collected.
		const auto &t = &trail;
		int i = t->size ();
		while (i) {
			int lit = (*t)[--i];
			Flags &f = flags (lit);
			if (lit == uip) // enough reasons collected // this somehow may not happen with chrono?
				break;
			if (!f.seen)
					continue;

			Var &v = var (lit);

			// units may be seen but they have decision reasons
			if (!v.level)
				continue;

			Clause *reason = v.reason;
			LOG ("Variable %d involved", vidx (lit));
			LOG (reason, "reason");
			feed_reason (pcs, reason);
		}

		// Also collect relevant unit clause {-lit} for each lit in unit_analyzed.
		// Without them we would miss some necessary assumptions.
		for (const auto &lit : unit_analyzed) {
			LOG ("unit %d reason with id %lld involved", -lit, unit_id (-lit));
			// unit clauses do not need to be pushed to pcs.clauses, since we can get
			// their cadical_id easily once returned from kitten
			feed_unit_reason (-lit);
		}
		STOP (allrprcollect);
	}

	// collects additional reasons necessary for deriving a proof of the 
	// minimized learned clause and feeds them to kitten
	// Here we misuse the added flag for marking work on the trail
	//
	void Internal::allrpr_collect_minimize_reasons(allrpr_proof_clauses &pcs) {
		START (allrprcollect);
		LOG ("ALLRPR COLLECT MINIMIZE REASONS");
		assert (citten);
		vector<int> units_flagged;
		for (const auto &lit : minimized) {
			Flags &f = flags (lit);
			if (f.removable) { // lit is relevant 
				Var &v = var (lit);
				Clause *reason = v.reason;
				LOG (reason, "relevant clause");
				feed_reason (pcs, reason);
				for (const auto &rlit : *reason) { // check for necessary units
					Flags &rf = flags (rlit);
					Var &v = var (rlit);
					if (v.level || rf.added)
						continue;
					if (rf.seen)
						continue;
					// unit not yet fed to kitten
					LOG ("relevant unit clause[%lld] %d", unit_id(-rlit), -rlit);
					feed_unit_reason (-rlit);
					rf.added = true; // dont feed units more than once
					units_flagged.push_back (rlit);
				}
			}
		}
		for (const auto &lit : units_flagged) {
			Flags &f = flags (lit);
			f.added = false;
		}
		STOP (allrprcollect);
	}

	// collect shrink reasons for literals in allrpr_shrunken
	//
	void Internal::allrpr_collect_shrink_reasons (allrpr_proof_clauses &pcs) {
		START (allrprcollect);
		LOG (allrpr_shrunken, "ALLRPR COLLECT SHRINK REASONS FOR ");
		vector<int> worked;
		for (const auto &lit : allrpr_shrunken) {
			Flags &f = flags (lit);
			assert (!f.added && !f.keep);
			f.added = true; // mark as open path
			worked.push_back (lit);
		}

		// go backwards through trail and collect necessary reasons
		const auto &t = &trail;
		int i = t->size ();
		while (i != 0) {
			int lit = (*t)[--i];
			Flags &f = flags (lit);
			if (!f.added || f.keep || f.poison)
				continue;
			Var &v = var (lit);
			if (!v.level) {
				if (f.seen)
					continue;
				LOG ("relevant unit clause[%lld] %d", unit_id (lit), lit);
				feed_unit_reason (lit);
				f.added = true;
				worked.push_back (lit);
			} else {
				Clause *reason = v.reason;
				assert (reason && f.removable);
				feed_reason (pcs, reason);
				for (const auto &rlit : *reason) {
					Flags &f = flags (rlit);
					f.added = true;
					worked.push_back (rlit);
				}
			}
		}
		// clean up added flag for each literal in worked
		for (const auto &lit : worked) {
			Flags &f = flags (lit);
			f.added = false;
		}
		allrpr_shrunken.clear ();
		STOP (allrprcollect);
	}

	void Internal::allrpr_build_lrat (allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR BUILD LRAT");
		std::vector<allrpr_proof_clause> &core = pcs.proof_clauses;
		unsigned last_learned_id = core[core.size() - 1].kitten_id; // kitten_id of last learned clause

		for (auto &pc: core) {
			if (!pc.learned) // allready proven clause (known to cadical)
				continue;
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
		// now all intermediate learned clauses are proven.
	}

	void Internal::allrpr_delete_intermediate_lrat (allrpr_proof_clauses &pcs) {
		START (allrprsolve);
		LOG ("ALLRPR DELETE INTERMEDIATE LRAT");
		// skip last learned clause, which is stored at the end of proof_clauses
		for (size_t i = 0; i < pcs.proof_clauses.size () - 1; i++) {
			allrpr_proof_clause &pc = pcs.proof_clauses[i];
			if (!pc.learned)
				continue;
			proof->delete_clause (pc.cadical_id, true, pc.literals);
		}
		STOP (allrprsolve);
	} 

	// Reconstructs a LRAT chain for the learned clause in internal->clause.
	// 
	void Internal::allrpr_kitten_catch_rat (int &uip, allrpr_proof_clauses &pcs) {
		START (allrprsolve);
		assert (lrat_chain.empty ());
		assert (citten);
	
		// Kitten is now fed with enough clauses.
		// We just need to assume the negation of the learned clause.
		// Some of the assumptions should then fail resulting in a proof of clause
		LOG (clause, "LEARNED CLAUSE: ");
		for (const auto &lit: clause) {
      if (lit == -uip)
        continue;
      LOG ("KITTEN ASSUME %d", -lit);
      kitten_assume_signed (citten, -lit);
    }
    LOG ("KITTEN ASSUME UIP %d", uip);
    kitten_assume_signed (citten, uip); // Assume uip last (not not uip)

		#ifdef LOGGING
  	if (opts.log)
  		kitten_set_logging (citten);
  	#endif

		kitten_track_antecedents (citten);
		kitten_solve (citten);

		// Now compute the clausal core and trace it. This will provide resolution
		// chains, which can be used for deriving an LRAT proof.
		kitten_compute_clausal_core (citten, nullptr);
		kitten_trace_core (citten, &pcs, extract_clause_from_kitten);
		allrpr_build_lrat (pcs);
		STOP (allrprsolve);
	}

}