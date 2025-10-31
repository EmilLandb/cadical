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
		int highest_trail = -1;
		for (const int &lit : *c) {
			LOG ("checking lit %d", lit);
			Var &v = var (lit);
			if (is_false (lit, pcs)) { // literal is falsified and (in the implication graph or implied)
				LOG ("lit %d falsity implied", lit);
				LOG ("lit %d marks %d", lit, allrpr_mark (lit, pcs));
				LOG ("lit %d marks %d", -lit, allrpr_mark (-lit, pcs));
				if (v.trail > highest_trail) // update highest trail position
					highest_trail = v.trail; 
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
		if (opts.allrprorder && val (prop_lit) && var (prop_lit).trail < highest_trail) {
			LOG ("Not qualified due to %d not having the highest trail rank", prop_lit);
			return false;
		}
		return true;
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

	// collects reasons necessary for deriving a proof of the learned clause
	// and feeds them to kitten 
	//
	void Internal::allrpr_collect_learn_reasons (int &uip, allrpr_proof_clauses &pcs) {
		START (allrprcollect);
		LOG ("ALLRPR COLLECT LEARNED REASONS");
		assert (conflict);
		assert (citten);
		assert (!opts.allrprextra);
		// add conflict clause. Will finally be falsified by the assumptions
		feed_reason (pcs, conflict);
		pcs.is_extra.push_back (0);  // TODO: remove later on

		int64_t added = 1; // number of added clauses

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
			feed_reason (pcs, reason);
			pcs.is_extra.push_back (0);  // TODO: remove later on
			added++;
		}

		// Also collect relevant unit clause {-lit} for each lit in unit_analyzed.
		// Without them we would miss some necessary assumptions.
		for (const auto &lit : unit_analyzed) {
			// unit clauses do not need to be pushed to pcs.clauses, since we can get
			// their cadical_id easily once returned from kitten
			feed_unit_reason (-lit);
			added++;
		}

		stats.allrpr.added += added;
		LOG ("ALLRPR COLLECT LEARNED REASONS added %lld clauses", added);
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
		assert (!opts.allrprextra);
		vector<int> units_flagged;
		int64_t added = 0; // number of added clauses
		for (const auto &lit : minimized) {
			Flags &f = flags (lit);
			if (f.removable) { // lit is relevant 
				Var &v = var (lit);
				Clause *reason = v.reason;
				feed_reason (pcs, reason);
				added++;
				for (const auto &rlit : *reason) { // check for necessary units
					Flags &rf = flags (rlit);
					Var &v = var (rlit);
					if (v.level || rf.added)
						continue;
					if (rf.seen)
						continue;
					// unit not yet fed to kitten
					feed_unit_reason (-rlit);
					added++;
					rf.added = true; // dont feed units more than once
					units_flagged.push_back (rlit);
				}
			}
		}
		for (const auto &lit : units_flagged) {
			Flags &f = flags (lit);
			f.added = false;
		}

		stats.allrpr.added += added;
		LOG ("ALLRPR COLLECT MINIMIZE REASONS added %lld clauses", added);
		STOP (allrprcollect);
	}

	// collect shrink reasons for literals in allrpr_shrunken
	//
	void Internal::allrpr_collect_shrink_reasons (allrpr_proof_clauses &pcs) {
		START (allrprcollect);
		LOG (allrpr_shrunken, "ALLRPR COLLECT SHRINK REASONS FOR ");
		assert (citten);
		assert (!opts.allrprextra);
		vector<int> worked;
		int64_t added = 0;
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
				feed_unit_reason (lit);
				added++;
				f.added = true;
				worked.push_back (lit);
			} else {
				Clause *reason = v.reason;
				assert (reason && f.removable);
				feed_reason (pcs, reason);
				pcs.is_extra.push_back (0);  // TODO: remove later on
				added++;
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

		stats.allrpr.added += added;
		LOG ("ALLRPR COLLECT SHRINK REASONS added %lld clauses", added);
		STOP (allrprcollect);
	}


	// collect all reasons and all possible propagation candidates (from trail)
	//
	void Internal::allrpr_collect_all (allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR COLLECT ALL");
		START (allrprcollect);
		assert (conflict);
		assert (citten);
		assert (opts.allrprtrail && opts.allrprextra);
		assert (opts.allrprtrail);
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

	void Internal::allrpr_collect_all_binary (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR COLLECT ALL BINARY");
		int64_t collected = 0;
		LOG (conflict, "Adding conflict");
		feed_reason (pcs, conflict);
		pcs.is_extra.push_back (0);
		collected++;
		// add base reasons
		LOG (base, "Adding base reasons for");
		for (const int &lit : base) {
			Var &v = var (lit);
			if (!v.level) {
				int64_t id = unit_id (lit);
				assert (unit_id (lit));
				collected++;
				feed_unit_reason (lit);
			} else if (v.reason) {
				collected++;
				feed_reason (pcs, v.reason);
				pcs.is_extra.push_back (0);
			} else {
				LOG ("No reason for %d", lit);
			}
		}

		// go backwards through trail
		const auto &t = &trail;
		int i = t->size ();	
		while (i) {
			int lit = (*t)[--i];
			
			LOG ("Checking watch list of %d", lit);
			Watches &ws = watches (lit);
			const const_watch_iterator eow = ws.end ();
			watch_iterator j = ws.begin ();
			while (j != eow) {
				const Watch w = *j++;
				if (!w.binary ())
					continue; 
				if (w.clause->garbage)
					continue;
				feed_reason (pcs, w.clause); // we need to dereference for the id anyways
				pcs.is_extra.push_back (1);
				collected++;
			}
		}
		LOG ("ALLRPR COLLECT ALL BINARY FINISHED COLLECTING %lld clauses", collected);
		//LOG (ids, "collected: ");
		stats.allrpr.added += collected;
	}

	// Initialize work by marking all literals that will be surely true (that are in the implication graph)
	void Internal::allrpr_mark_graph (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR MARK GRAPH");
		START (allrprcollect);
		// mark learned clause literals as targets for minimization
		LOG ("Setting learned clause literals as minimization targets...");
		for (const int &lit : clause) {
			set_target (-lit, pcs);
		}
		// go backwards through trail
		const auto &t = &trail;
		int i = t->size ();	
		while (i) {
			int lit = (*t)[--i];
			assert (!is_true (lit, pcs));
			assert (!is_true (-lit, pcs));
			Var &v = var (lit);
			if (!v.level) { // unit 
				LOG ("marking unit %d", lit);
				set_true (lit, pcs);
				base.push_back (lit);
				continue;
			}
			Flags &f = flags (lit);
			if (f.seen || f.removable) {
				LOG ("marking %s %s %d", f.seen ? "seen" : "", f.removable ? "removable" : "", lit);
				set_true (lit, pcs);
				base.push_back (lit);
			}
		}
		LOG (base, "marked");
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
				int64_t id = unit_id (lit);
				assert (unit_id (lit));
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
// -------------------------------------------------------------------------- //
	// Trying to simulate propagation with the different order
	// 
	void Internal::allrpr_collect_prop (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR COLLECT PROP");
		START (allrprcollect);
		int64_t collected = 0;
		// set up minimization target marks
		for (const int &ll : clause) {
			set_target (-ll, pcs); // implication graph node
		}
		vector<int> prop_stack;
		vector<int> mini_trail;
		for (const int &ll : clause) { 
			//unset_target (-ll, pcs); // remove targeting 
			set_true (-ll, pcs);     // assume
			set_worked (-ll, pcs);
			prop_stack.push_back (-ll);

			// Now look in prop stack for binaries
			while (!prop_stack.empty ()) {
				const int lit = prop_stack.back ();
				prop_stack.pop_back ();
				mini_trail.push_back (lit);
				LOG ("Checking watch list of %d for binary and ternary clauses", -lit);
				Watches &ws = watches (-lit);
				const const_watch_iterator eow = ws.end ();
				watch_iterator i = ws.begin ();
				// First find all binary clauses
				while (i != eow) {
					const Watch w = *i++;
					if (w.clause->garbage)
						continue;
					if (w.binary ()) {
						if (is_target (w.blit, pcs)) {
							LOG (w.clause, "Found minimization path for %d through", w.blit);
							LOG (mini_trail, "minimization trail:");
						} else
							LOG (w.clause, "Found");
						if (!is_true (w.blit, pcs)) {
							LOG ("marking %d as true and pushing to prop_stack", w.blit);
							set_true (w.blit, pcs);
							prop_stack.push_back (w.blit);
							//mini_trail.push_back (w.blit);
							collected++;
						} else {
							LOG ("already added %d to prop_stack", w.blit);
						}	
					} 
					else if (w.size == 3) {
						LOG (w.clause, "Checking ternary");
						int found_possible = 0;
						bool satisfied = false;
						for (const int &tl : *w.clause) {
							if (is_true (tl, pcs)) {
								satisfied = true;
								break;
							}
							if (is_true (-tl, pcs)) // i.e. tl is falsified, holds for at least 'lit'
								continue; 
							if (!found_possible) {
								LOG ("possible new propagation for %d", tl);
								found_possible = tl;
							} else {
								LOG ("second non-falsified %d", tl);	
								found_possible = 0; // this should work since we can only set found possible to tl once and only once back to 0	
							} 
						}
						if (found_possible && !satisfied) {
							if (is_target (found_possible, pcs)) {
								LOG (w.clause, "Found minimization path for %d through", found_possible);	
								LOG (mini_trail, "minimization trail:");
							}
							LOG ("marking %d as true and pushing to prop_stack", found_possible);
							set_true (found_possible, pcs);
							prop_stack.push_back (found_possible);
							collected++;
						} else {
							LOG (w.clause, "No new propagations found for");
						}
					} 
					//feed_reason (pcs, w.clause);
					//pcs.is_extra.push_back (1);
				}
			}
			// set learned lit ll as target again
			set_target (-ll, pcs);
			set_false (-ll, pcs);
			mini_trail.clear ();
		}
		STOP (allrprcollect);
		LOG ("ALLRPR COLLECT MORE FINISHED COLLECTING %lld clauses", collected);
	}
// -------------------------------------------------------------------------- //

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
		int extraincore = 0; // TODO: remove later on
		int extraisred = 0; // TODO: remove later on
		int extragrternary = 0; // TODO: remove later on
		for (auto &pc: core) {
			if (!pc.learned) { // allready proven clause (known to cadical)
				norig++;
				// TODO: vvv remove later on vvv----------------------------------------
				if (pc.literals.size () == 1) // units are not stored in pcs.reasons
					continue;
				bool is_extra = pcs.is_extra[pc.allrpr_id];
				Clause *cadiclause = pcs.reasons[pc.allrpr_id];
				if (is_extra) {
					if (cadiclause->redundant) {
						LOG (cadiclause, "is redundant extra clause");
						extraisred++;
					} else {
						LOG (cadiclause, "is irredundant extra clause");
					}
					if (pc.literals.size () > 3) {
						LOG (cadiclause, "is extra clause greater than ternary");
						extragrternary++;
					}
					extraincore++;
				}
				// TODO: ^^^ remove later on ^^^----------------------------------------
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
			if (extraisred) { 
				stats.allrpr.redextraincore++; // core contains a redundant extra clause
				stats.allrpr.redextras += extraisred;
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
			proof->delete_clause (pc.cadical_id, true, pc.literals);
		}
		STOP (allrprlrat);
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
  		//kitten_set_logging (citten);
  	#endif

    // shuffle assumptions for the possibility of a smaller core failing clause
  	// this got moved because of collect more.
    // if (opts.allrprshufflea) {
    //	kitten_shuffle_assumptions (citten);
    //}
    if (opts.allrprshufflec) {
    	kitten_shuffle_clauses (citten);
    }

		kitten_track_antecedents (citten);
		kitten_solve (citten);

		// Now compute the clausal core and trace it. This will provide resolution
		// chains, which can be used for deriving an LRAT proof.
		kitten_compute_clausal_core (citten, nullptr);
		LOG (trail, "trail:"); // TODO: remove later on
		kitten_trace_core (citten, &pcs, extract_clause_from_kitten);
		STOP (allrprsolve);
		
		allrpr_build_lrat (pcs);
		vector<int> &klause = 
					pcs.proof_clauses[pcs.proof_clauses.size () - 1].literals;
		const size_t old_size = clause.size ();
		const size_t new_size = klause.size ();
		if (old_size > new_size) {
			LOG (clause, "Successful further minimization of");
			clause = std::move(klause);
			//clause.clear ();
			//for (const int &lit : pcs.proof_clauses[pcs.proof_clauses.size () - 1].literals) {
			//	clause.push_back (lit);
			//}
			LOG (clause, "to");	
			stats.allrpr.nminimized++;
			stats.allrpr.sminimized += old_size - new_size;
		}
		stats.allrpr.kittencalls++;
		stats.allrpr.slearnedlits += (int64_t) new_size;
		// this is just for checking, how this can happen. Comment out later!
		//assert (clause.size () == pcs.proof_clauses[pcs.proof_clauses.size () - 1].literals.size ());
	}

}	