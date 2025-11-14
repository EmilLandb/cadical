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
} // end extern "C"

	
	inline void Internal::feed_reason (allrpr_proof_clauses &pcs, Clause *reason) {
		LOG (reason, "Adding reason");
		const unsigned id = pcs.reasons.size();
		citten_clause_with_id (citten, id, reason->size, reason->literals);
		pcs.reasons.push_back	(reason);
	}

	inline void Internal::feed_unit_reason (int unit) {
		int64_t id = unit_id (unit);
		assert (unit_id (unit));
		LOG ("Adding unit clause[%lld] %d", id, unit);
		citten_clause_with_id (citten, id, 1, &unit);
	}

	// collect all reasons and all possible propagation candidates (from trail)
	//
	void Internal::allrpr_collect_all (allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR COLLECT ALL");
		START (allrprcollect);
		assert (conflict);
		assert (citten);
		feed_reason (pcs, conflict);
    	pcs.is_extra.push_back (0);  // TODO: remove later on
		int64_t added = 1;

		// go backwards through trail
		const auto &t = &trail;
		int i = t->size ();	
		while (i) {
			int lit = (*t)[--i];
			Var &v = var (lit);
			if (!v.level) {
				feed_unit_reason (lit);
			}
			Clause *reason = v.reason;
			// && !reason->garbage <-- this also leads to problems...
			if (reason && reason->size) { // weird situations where mock propagator adds size 0 clauses
				added++;
				feed_reason (pcs, reason);
				pcs.is_extra.push_back (0); // TODO: remove later on
			}

			LOG ("Checking watch list of %d", lit);
			Watches &ws = watches (lit);
			const const_watch_iterator eow = ws.end ();
			watch_iterator j = ws.begin ();

			while (j != eow) {
				const Watch w = *j++;
				LOG (w.clause, "Checking");
				if (w.clause->garbage) {
					LOG (w.clause, "Skipping garbage");
					continue;
				}
				if (w.clause == reason || w.clause == conflict) {
					LOG (w.clause, "Skipping %s", w.clause == reason ? "reason" : "conflict");
					continue;
				}
				if (val (w.blit) > 0 && w.blit != lit) {
					LOG (w.clause, "Skipping doubly satisfied");
					continue;
				}
				// check clause for being a propagation candidate.
				// i.e. all literals false except for lit, which is satisfied
				bool relevant = true;
				for (const auto &l : *w.clause) {
					if (val (l) < 0)
						continue;
					if (l != lit) {
						LOG ("Skipping due to unfalsified literal %d != %d", l, lit);
						relevant = false;
						break;
					}
				}
				if (relevant) {
					LOG (w.clause, "possibly relevant");
					added++;
					feed_reason (pcs, w.clause);
					pcs.is_extra.push_back (1);  // TODO: remove later on
				}
			}
		}
		stats.allrpr.added += added;
		STOP (allrprcollect);
		LOG ("ALLRPR COLLECT ALL added %lld clauses", added);
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
	void Internal::allrpr_kitten_catch_rat (int &uip, allrpr_proof_clauses &pcs) {
		START (allrprsolve);
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
		kitten_compute_clausal_core (citten, nullptr);
		kitten_trace_core (citten, &pcs, extract_clause_from_kitten);
		stats.allrpr.kittencalls++;
		STOP (allrprsolve);
	}

}	