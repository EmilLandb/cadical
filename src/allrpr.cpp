#include "internal.hpp"

namespace CaDiCaL {

	#define INVALID64 INT64_MAX
	#define INVALID UINT_MAX

	// -------------------------------------------------------------------------//
	//      |I|B|W|T|T
	//	    |N|A|O|R|R
	//      |K|S|R|G|U
	//      |T|E|K|T|E
	// 0|0|0|0|0|0|0|0
	constexpr signed char TRUE   = 1 << 0;
	constexpr signed char TARGET = 1 << 1;
	constexpr signed char WORKED = 1 << 2;
	constexpr signed char BASE = 1 << 3;
	constexpr signed char IN_KITTEN = 1 << 4;

	signed char &Internal::allrpr_mark (int lit, allrpr_proof_clauses &pcs) {
		assert (internal->vlit (lit) < pcs.marks.size ());
		return pcs.marks[internal->vlit (lit)];
	}

	const signed char &Internal::allrpr_mark(int lit, const allrpr_proof_clauses &pcs) const {
    assert(internal->vlit(lit) < pcs.marks.size());
    return pcs.marks[internal->vlit(lit)];
	}

	inline bool Internal::is_true (int lit, const allrpr_proof_clauses &pcs) const {
	 return allrpr_mark (lit, pcs) & TRUE; 
	}

	inline bool Internal::is_false (int lit, const allrpr_proof_clauses &pcs) const {
	 return allrpr_mark (-lit, pcs) & TRUE; 
	}

	inline bool Internal::is_target (int lit, const allrpr_proof_clauses &pcs) const {
	 return allrpr_mark (lit, pcs) & TARGET; 
	}

	inline bool Internal::is_worked (int lit, const allrpr_proof_clauses &pcs) const {
	 return allrpr_mark (lit, pcs) & WORKED; 
	}

	inline bool Internal::is_in_kitten (int lit, const allrpr_proof_clauses &pcs) const {
		return allrpr_mark (lit, pcs) & IN_KITTEN;
	}

	inline bool Internal::is_base (int lit, const allrpr_proof_clauses &pcs) const {
		return allrpr_mark (lit, pcs) & BASE; 
	}

	inline void Internal::set_true (int lit, allrpr_proof_clauses &pcs) {
	 allrpr_mark (lit, pcs) |= TRUE; 
	}

	inline void Internal::set_false (int lit, allrpr_proof_clauses &pcs) {
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

	inline void Internal::set_in_kitten (int lit, allrpr_proof_clauses &pcs) {
		allrpr_mark (lit, pcs) |= IN_KITTEN;
	}
	
	inline void Internal::set_base (int lit, allrpr_proof_clauses &pcs) {
	 allrpr_mark (lit, pcs) |= BASE; 
	}

	// -------------------------------------------------------------------------//

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

	// check whether kitten needs to be reset and if so clean up.
	//
	void Internal::allrpr_check_kitten_and_pcs () {
		if (citten && allrpr_need_reset) {
      // this is true if mark_garbage, mark_added or mark_removed was called
      // on a clause for which c->added holds. All pointers should still be 
      // valid but the Kitten clause base is still corrupted. Before resetting
      // we need to unflag all c->added clauses and clear the clause map.
      // If collection happened, the flags and reasons would've been cleared 
      // directly before garbage collection.
      if (!(allrpr_last_reduction < stats.reductions)) {
        LOG ("Some clause in Kitten is out of sync. Resetting...");
        allrpr_clear_added_flags ();
      }
      else {
        LOG ("Garbage collection ran previously. Resetting...");
        allrpr_last_reduction = stats.reductions;  
      }
      kitten_clear (citten);
      allrpr_reset_citten ();
      allrpr_need_reset = false;        
    }
    if (!citten || allrpr_pcs.marks.size () <= (size_t) 2 * max_var + 1) {
      LOG ("Initializing fresh Kitten...");
      if (opts.allrprreport)
        printf ("\nKIT Kitten Size 0\n"); // TODO Remove
      allrpr_init_citten ();
      kitten_track_antecedents (citten); // Not needed w/o LRAT ?
      LOG ("Clearing added flags and allrpr_pcs.reasons...");
      // Here we also need to clear flags and reasons because Kitten got reset
      // in elim or sweep.
      if (!allrpr_pcs.reasons.empty ())
        for (Clause *c : allrpr_pcs.reasons) {
          if (c->moved) {
            LOG (c->copy, "(copy) clearing added in");
            (c->copy)->added = false;
          } else {
            LOG (c, "clearing added in");
            assert (c->added);
            c->added = false;
          }
        }
      allrpr_pcs.reasons.clear ();
      allrpr_pcs.marks.resize (2 * max_var + 3); 
      fill(allrpr_pcs.marks.begin(), allrpr_pcs.marks.end(), 0);
      
      allrpr_pcs.internal = this;
      allrpr_last_size_after_reset = 0;
      stats.allrpr.kittenresets++;
    }
	}

	// Clearing the added flags in clauses that were fed to kitten.
	// This must always be used before garbage collection, since afterwards the 
	// pointers in allrpr_pcs.reason may be dangling
	//
	void Internal::allrpr_clear_added_flags () {
		LOG ("Clearing added flags and allrpr_pcs.reasons");
		allrpr_need_reset = true;
    for (Clause *c : allrpr_pcs.reasons) {
      if (c->moved) {
        LOG (c->copy, "(copy) clearing added in");
        (c->copy)->added = false;
      } else {
      	LOG (c, "clearing added in");
        assert (c->added);
        c->added = false;
      }
    }
    allrpr_pcs.reasons.clear ();
    LOG ("allrpr_pcs.reason.size () = %zu", allrpr_pcs.reasons.size ());
	}

	// Sort the successfully shrunken clause in descending trail order
	// and then move literals that are uips of slices to the back
	// Idea: Latest assumed literals have the highest chance of being implied 
	// by others in kitten and can then be removed.
	// Removing the mentioned uip literals will definitely improve the glue 
	// of the clause
	void Internal::allrpr_sort_shrunken() {
		START (allrprreorder);
		const int size = (int) clause.size ();
		if (size < 3) {
			STOP (allrprreorder);
			return;
		}
		LOG ("ALLRPR SORT SHRUNKEN");
		minimize_sort_clause ();
		reverse (clause.begin (), clause.end ());

		vector<int> slice_uips;
		vector<int> non_uips = {clause[0]}; // keep actual uip at the front

		int prev_lvl = var (clause[0]).level;
		int this_lvl = var (clause[1]).level;
		int next_lvl;
		for (auto i = 1; i < size - 1; i++) {
			next_lvl = var (clause[i+1]).level;
			if (this_lvl == prev_lvl || this_lvl == next_lvl) { // no slice uip
				non_uips.push_back (clause[i]);
			} else {
				slice_uips.push_back (clause[i]);
			}

			prev_lvl = this_lvl;
			this_lvl = next_lvl;
		}
		// process last
		if (this_lvl != prev_lvl)
			slice_uips.push_back (clause[size-1]);
		else 
			non_uips.push_back (clause[size-1]);


		for (size_t i = 0; i < non_uips.size (); i++)
			clause[i] = non_uips[i];
		for (size_t i = non_uips.size(); i < (size_t) size; i++)
			clause[i] = slice_uips[i - non_uips.size()];
		LOG (clause, "sorted clause:");
		STOP (allrprreorder);
	}

	// Checks, whether a clause is qualified for being fed into kitten.
	// I.e. if the clause could propagate given the current set of true literals
	// and isn't garbage. If the clause is qualified, the possibly propagating
	// literal is written into prop_lit.
	//
	bool Internal::clause_is_qualified (Clause *c, int &prop_lit, const allrpr_proof_clauses &pcs) {
		LOG (c, "Checking qualification of");
		assert (!prop_lit);
		if (c->garbage) {
			LOG (c, "Not qualified garbage");
			return false;
		}

		// A clause would propagate, if its only non-false literal has the highest
		// trail position among literals in the clause
		for (const int &lit : *c) {
			LOG ("checking lit %d", lit);
			if (is_false (lit, pcs)) { // literal is falsified and (in the implication graph or implied)
				LOG ("lit %d falsity implied", lit);
				continue;
			}
			if (prop_lit) {
				LOG ("Not qualified due to %d being the second non-marked/non-false literal", -lit);
				return false;
			}
			prop_lit = lit; // This may propagate, if it is the only non-false literal
		}
		return true;
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
		if (pc.literals.size () == 1) {
			LOG (pc.literals, "traced unit");
		}
		else
			LOG (pc.literals, "traced [%lld] %s", learned ? -1 : pc.cadical_id, learned ? "kit learned" : "original");
  	core.push_back (pc);
	}
	*/

	// Lightweight callback function that just extracts the final learned clause
	// for checking whether and in which way minimization was successful.
	// This is used in allrpr_kitten_attempt_minimize, where we don't care about 
	// producing the LRAT proof yet
	//
	static void get_final_from_core_with_bumping (void *state, bool learned, 
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
			// also add to analyze for bumping if not added yet, i.e. if not 'seen'
			Flags &f = internal->flags (lit);
			if (!f.seen) {
				LOG ("Unseen literal %d marked for bumping", lit);
				f.seen = true;
				internal->analyzed.push_back (lit);
			}
		}
	#ifdef LOGGING
		LOG (final, "failing clause");
	#endif
	}

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
	
	// Feeding a clause to kitten and logging it in pcs.reasons.
  // The kitten clause can later on be mapped to a cadical clause by using the
	// given id, which corresponds to the index in pcs.reasons.
	//
	inline void Internal::feed_reason (allrpr_proof_clauses &pcs, Clause *reason) {
		LOG (reason, "Adding reason giving allrpr_id %zu", pcs.reasons.size ());
		const unsigned id = pcs.reasons.size();
		citten_clause_with_id (citten, id, reason->size, reason->literals);
		pcs.reasons.push_back	(reason);
	}

	// Feeding a unit clause to kitten. Here we do not log this into the 
	// pcs.reasons, since there is no corresponding cadical clause in the sense of 
	// a struct Clause. We directly attach the unit_id in this case.
	//
	inline void Internal::feed_unit_reason (int unit) {
		//int64_t id = unit_id (unit);
		//assert (unit_id (unit));
		LOG ("Adding unit clause[%lld] %d", -1, unit);
		citten_clause_with_id (citten, 0, 1, &unit);
	}

	// Sets the literals in the implication graph between the learned clause and
	// the conflict as base literals and to true.
	// The literals in the conflict clause are all falsified and therefore, their
	// negation is set to true. The same is done for the learned clause literals.
	// 
	// 
	void Internal::allrpr_mark_graph (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR MARK GRAPH");
		START (allrprcollect);

		// mark all conflict clause literals negations as true
		LOG ("Setting negated conflict clause literals to true");
		for (const int &lit : *conflict) {
			LOG ("setting true %d", -lit);
			set_true (-lit, pcs);
			set_base (lit, pcs); // TODO: Check if removable or useful
			set_base (-lit, pcs); 
			base.push_back (-lit);
		}
		// mark all learned clause literals negations as target
		LOG ("Setting negated learend clause literals as target");
		int work = (int) clause.size ();
		for (const int &lit : clause) {
			LOG ("setting target %d", -lit);
			set_target (-lit, pcs);
			set_base (-lit, pcs);
			set_base (lit, pcs); // TODO: Check if removable or useful
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
					set_base (-rlit, pcs);
					set_base (rlit, pcs); // TODO: Check if removable or useful
					base.push_back (-rlit);			
				}
			}
		}
		for (const int &lit : base) {
			allrpr_mark (lit, pcs) &= ~TARGET; 
		}
		LOG (base, "base:");
		STOP (allrprcollect);
	}

	// Collect extra clauses starting from base. Filter clauses that contain too
	// many non-base literals, i.e. are further away from the present 
	// implication graph.
	//
	void Internal::allrpr_collect_more_dist_filter (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR COLLECT MORE");
		START (allrprcollect);
		vector<Clause*> unmarkcls;
		vector<int> work;
		const int old_kitten_size = (int) pcs.reasons.size ();
		int basecls = 0;
		int extracls = 0;
		int wouldbase = 0;
		// init work stack in order of assumption
		if (!conflict->added) {
			LOG (conflict, "Adding conflict");
			feed_reason (pcs, conflict);
			assert (!conflict->added);
			conflict->added = true;
			pcs.is_extra.push_back (0);  // TODO: remove later on
			basecls++;
		} else {
			LOG (conflict, "skipping already added");
			wouldbase++;
		}
		// add base reasons and queue them up for work
		LOG (base, "Adding base reasons for");
		for (const int &lit : base) {
			Var &v = var (lit);
			if (!v.level) {
				basecls++;
				feed_unit_reason (lit);
			} else if (v.reason && !v.reason->added) {
				basecls++;
				feed_reason (pcs, v.reason);
				pcs.is_extra.push_back (0);
				assert (!v.reason->added);
				v.reason->added = true;
			} 
			else if (v.reason && v.reason->added) {
				LOG (v.reason, "skipping already added");
				wouldbase++;
			}
			else {
				LOG ("No reason for %d", lit);
			}
			work.push_back (lit);
			set_worked (lit, pcs);
		}

		LOG (work, "initialized work to");
		// Now start at the end of work and look for further propagations given
		// the valuations by the marks. If a literal could propagate, we push it 
		// onto work and mark it.
		while (!work.empty () && extracls < opts.allrpraddthresh) {
			int lit = work.back ();
			assert (is_worked (lit, pcs));
			work.pop_back ();
			LOG ("working on %d", lit);

			if (opts.allrprskipearly) {
				if (is_in_kitten (lit, pcs)) {
					LOG ("%d watch list clauses are already in kitten", -lit);
					continue;
				}
				set_in_kitten (lit, pcs);
			}
				
			LOG ("Checking watch list of %d", -lit);
			Watches &ws = watches (-lit);
			const const_watch_iterator eow = ws.end ();
			watch_iterator j = ws.begin ();

			while (j != eow) {
				const Watch w = *j++;
				int prop_lit = 0;
				if (w.size > 4) // TODO: remove after tests
					continue;
				if (w.clause->added) {
					LOG (w.clause, "Skipping already added clause");
					continue;
				}
				// Filter clauses whose dist is too high -------------------------------
				int nb_in_c = 0;
				for (const int &l : *w.clause) {
					if (!is_base (l, pcs))
						nb_in_c++;
				}
				if (nb_in_c > opts.allrprdist) {
					LOG (w.clause, "skipping too high dist");
					w.clause->added = true; // mark added so it is skipped in the future
					unmarkcls.push_back (w.clause);
					continue;
				}
				// ---------------------------------------------------------------------

				if (clause_is_qualified (w.clause, prop_lit, pcs)) {
					if (extracls >= opts.allrpraddthresh) {
						LOG ("Reached addition threshold of %lld", opts.allrpraddthresh);
						break;
					}
					if (!prop_lit) {
						LOG (w.clause, "Adding possibly conflict");
						feed_reason (pcs, w.clause);
						pcs.is_extra.push_back (1);
						extracls++;
						w.clause->added = true;
						continue;
					} 
					else {
						LOG (w.clause, "Adding possibly propagating %d", prop_lit);
						feed_reason (pcs, w.clause);
						pcs.is_extra.push_back (1);
						extracls++;
						w.clause->added = true;
						
						// Mark and push to work, if wasn't work already
						if (!is_true (prop_lit, pcs)) {
							LOG ("%d is not set to true. setting true flag...", prop_lit);
							set_true (prop_lit, pcs);
						}
						// if the watch list of the literal wasn't yet traversed queue it up for work
						if (!is_in_kitten (prop_lit, pcs) && !is_worked (prop_lit, pcs)) {
							LOG ("%d wasn't in work yet. pushing to work...", prop_lit);
							work.push_back (prop_lit);
							set_worked (prop_lit, pcs);
						}
					} 
				}
			}
		}
		LOG ("ALLRPR COLLECT MORE FINISHED COLLECTING %lld clauses", basecls + extracls);
		LOG ("pcs.reasons (size: %zu):", pcs.reasons.size ());
		stats.allrpr.added += basecls + extracls;
		stats.allrpr.baseadded += basecls;
		stats.allrpr.extradded += extracls;
		stats.allrpr.baseskipped += wouldbase;
		if (opts.allrprreport) {
			printf ("KIT added baseclauses %d\n", basecls);
			printf ("KIT skipped baseclauses %d\n", wouldbase);
			printf ("KIT added extraclauses %d\n", extracls);
		}

		const int kitten_size = old_kitten_size + basecls + extracls;
		// Update if fresh kitten
		if (!old_kitten_size) {
			allrpr_last_size_after_reset = kitten_size;
		} 
		// Further clauses were added. Maybe reset kitten if too many new clauses
		else if (kitten_size > 3 * allrpr_last_size_after_reset && kitten_size > opts.allrprresethresh) { 
			if (opts.allrprreport) {
				printf ("KIT last size after reset %d\n", allrpr_last_size_after_reset);
				printf ("KIT force reset\n");
			}
			allrpr_need_reset = true;
		}

		// clean up
		for (Clause* c : unmarkcls) {
			assert (c->added);
			c->added = false;
		}
		STOP (allrprcollect);
	}

// ----------------------------------------------------------------------------//
	// Collect extra clauses starting from base. Filter clauses that contain too
	// many non-base literals, i.e. are further away from the present 
	// implication graph.
	//

	void Internal::allrpr_collect_more_dist_filter_BFS (vector<int> &base, allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR COLLECT MORE");
		START (allrprcollect);
		vector<Clause*> unmarkcls;
		vector<int> work;
		const int old_kitten_size = (int) pcs.reasons.size ();
		int basecls = 0;
		int extracls = 0;
		int wouldbase = 0;

		if (!conflict->added) {
			LOG (conflict, "Adding conflict");
			feed_reason (pcs, conflict);
			assert (!conflict->added);
			conflict->added = true;
			pcs.is_extra.push_back (0);  // TODO: remove later on
			basecls++;
		} else {
			LOG (conflict, "skipping already added");
			wouldbase++;
		}
		// add base reasons and queue them up for work
		LOG (base, "Adding base reasons for");
		for (const int &lit : base) {
			Var &v = var (lit);
			if (!v.level) {
				basecls++;
				feed_unit_reason (lit);
			} else if (v.reason && !v.reason->added) {
				basecls++;
				feed_reason (pcs, v.reason);
				pcs.is_extra.push_back (0);
				assert (!v.reason->added);
				v.reason->added = true;
			} 
			else if (v.reason && v.reason->added) {
				LOG (v.reason, "skipping already added");
				wouldbase++;
			}
			else {
				LOG ("No reason for %d", lit);
			}
			//work.push_back (lit);
			//set_worked (lit, pcs);
		}
		for (const int &lit : clause) {
			work.push_back (lit);
			set_worked (lit, pcs);			
		}
		if (opts.allrprextra) {
			LOG (work, "initialized work to");
			// Now start at the end of work and look for further propagations given
			// the valuations by the marks. If a literal could propagate, we push it 
			// onto work and mark it.
			size_t idx = 0;
			while (idx < work.size () && extracls < opts.allrpraddthresh) {
				int lit = work[idx];
				++idx;
				assert (is_worked (lit, pcs));
				LOG ("working on %d", lit);
				
				if (opts.allrprskipearly) {
					if (is_in_kitten (lit, pcs)) {
					LOG ("%d watch list clauses probably are already in kitten", -lit);
					continue;
					}
					set_in_kitten (lit, pcs);	
				}
				
				LOG ("Checking watch list of %d", -lit);
				Watches &ws = watches (-lit);
				const const_watch_iterator eow = ws.end ();
				watch_iterator j = ws.begin ();
				while (j != eow) {
					const Watch w = *j++;
					int prop_lit = 0;
					if (w.size > opts.allrprextmaxsize)
						continue;
					if (w.clause->added) {
						LOG (w.clause, "Skipping already added clause");
						continue;
					}
					// Filter clauses whose dist is too high -------------------------------
					int nb_in_c = 0;
					for (const int &l : *w.clause) {
						if (!is_base (l, pcs))
							nb_in_c++;
					}
					if (nb_in_c > opts.allrprdist) {
						//LOG (w.clause, "skipping too high dist");
						w.clause->added = true; // mark added so it is skipped in the future
						unmarkcls.push_back (w.clause);
						continue;
					}
					// ---------------------------------------------------------------------

					if (clause_is_qualified (w.clause, prop_lit, pcs)) {
						if (extracls >= opts.allrpraddthresh) {
							LOG ("Reached addition threshold of %lld", opts.allrpraddthresh);
							break;
						}
						if (!prop_lit) {
							LOG (w.clause, "Adding possibly conflict");
							feed_reason (pcs, w.clause);
							pcs.is_extra.push_back (1);
							extracls++;
							w.clause->added = true;
							continue;
						} 
						else {
							LOG (w.clause, "Adding possibly propagating %d", prop_lit);
							feed_reason (pcs, w.clause);
							pcs.is_extra.push_back (1);
							extracls++;
							w.clause->added = true;
							
							// Mark and push to work, if wasn't work already
							if (!is_true (prop_lit, pcs)) {
								LOG ("%d is not set to true. setting true flag...", prop_lit);
								set_true (prop_lit, pcs);
							}
							// if the watch list of the literal wasn't yet traversed queue it up for work
							if (!is_in_kitten (prop_lit, pcs) && !is_worked (prop_lit, pcs)) {
								LOG ("%d wasn't in work yet. pushing to work...", prop_lit);
								work.push_back (prop_lit);
								set_worked (prop_lit, pcs);
							}
						} 
					}
				}
			}
		}
		
		LOG ("ALLRPR COLLECT MORE FINISHED COLLECTING %lld clauses", basecls + extracls);
		LOG ("pcs.reasons (size: %zu):", pcs.reasons.size ());
		stats.allrpr.added += basecls + extracls;
		stats.allrpr.baseadded += basecls;
		stats.allrpr.extradded += extracls;
		stats.allrpr.baseskipped += wouldbase;
		if (opts.allrprreport) {
			printf ("KIT added baseclauses %d\n", basecls);
			printf ("KIT skipped baseclauses %d\n", wouldbase);
			printf ("KIT added extraclauses %d\n", extracls);
		}

		// Update if fresh kitten
		if (!old_kitten_size) {
			allrpr_last_size_after_reset = basecls + extracls;
		} 

		// Further clauses were added. Maybe reset kitten if too many new clauses
		else if ((old_kitten_size + basecls + extracls) > 3 * allrpr_last_size_after_reset) { 
			if (opts.allrprreport) {
				printf ("KIT last size after reset %d\n", allrpr_last_size_after_reset);
				printf ("KIT force reset\n");
			}
			allrpr_need_reset = true;
		}

		// clean up
		for (Clause* c : unmarkcls) {
			assert (c->added);
			c->added = false;
		}
		STOP (allrprcollect);
	}

// ----------------------------------------------------------------------------//

	// Build the LRAT chain(s) for the core learned clause. For intermediate 
	// learned clauses the chains also have to be built and logged before finally,
	// later in analyze () the LRAT chain for the core learned clause is logged.
	//
	void Internal::allrpr_build_lrat (allrpr_proof_clauses &pcs) {
		LOG ("ALLRPR BUILD LRAT");
		LOG ("Core size: %zu", pcs.proof_clauses.size ());
		START (allrprlrat);
		auto &core = pcs.proof_clauses;
		const auto &final_clause = core.back();
		LOG (final_clause.literals, "final clause of size %zu has literals:",final_clause.literals.size ());
		// found weird trace where the learned clause already existed
		// here the chain is just the existing clauses id
		if (!final_clause.learned) { 
			LOG (final_clause.literals, "deriving LRAT proof for");
			lrat_chain.push_back (final_clause.cadical_id);
			LOG (lrat_chain, "LRAT chain:");
			return;
		}

		const unsigned last_learned_id = final_clause.kitten_id;
		for (auto &pc: core) {
			if (!pc.learned) // allready proven clause (known to cadical)
				continue;
			LOG (pc.literals, "deriving LRAT proof for ");
			assert (pc.cadical_id == INVALID64);
			// build chain of cadical ids
			for (const auto &kitten_id : pc.chain) {
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
		STOP (allrprlrat);
	}

	// Deletion of intermediate learned clause chains after the final 
	// core learned clauses proof is logged.
	//
	void Internal::allrpr_delete_intermediate_lrat (const allrpr_proof_clauses &pcs) {
		//START (allrprlrat);
		LOG ("ALLRPR DELETE INTERMEDIATE LRAT");
		const auto &core = pcs.proof_clauses;

		// skip last learned clause, which is stored at the end of proof_clauses
		for (size_t i = 0; i + 1 < core.size (); i++) {
			const auto &pc = core[i];
			if (!pc.learned)
				continue;

			LOG ("Deleting clause[%lld]", pc.cadical_id);
			proof->delete_clause (pc.cadical_id, true, pc.literals);
		}
		LOG ("ALLRPR DELETE INTERMEDIATE LRAT FINISHED");
		//STOP (allrprlrat);
	} 

 	// Checks if various preconditions for further minimization attempts are met
	//
	bool Internal::allrpr_try_minimize (int glue, int size, const int old_size) const {
		// the first three filters are the same as in likely_to_be_kept_clause
		if (glue <= tier2[false])
			return true;
		if (glue > lim.keptglue)
			return false;
		if (size > lim.keptsize)
			return false;
		if (opts.allrprfiltershrink && old_size == size)
			return false;
		return true;
	}

	// Called as the final round of attempted minimization. Here we finally also
	// produce the proof
	// 
	void Internal::allrpr_kitten_catch_rat (int uip, allrpr_mini_pcs &mini_pcs) {
		START (allrprsolve);
		assert (citten);
		// assume the negation of the learned clause, which should unsatisfy the 
		// conflict clause.
		// if !uip then the empty clause was already derived.
		if (uip) { 
			LOG (clause, "LEARNED CLAUSE: ");
			for (const auto &lit: clause) {
      	LOG ("KITTEN ASSUME %d", -lit);
      	kitten_assume_signed (citten, -lit);
    	}
    	LOG ("Solving kitten...");
			kitten_solve (citten);
			// Now compute the clausal core and trace it. This will provide resolution
			// chains, which can be used for deriving an LRAT proof.
			LOG ("Computing clausal core...");
			mini_pcs.cadi_core_clauses = kitten_compute_clausal_core (citten, &mini_pcs.kitten_core_clauses);
			LOG ("cadical core clauses: %lld", mini_pcs.cadi_core_clauses);
			LOG ("kitten core clauses: %lld", mini_pcs.kitten_core_clauses);
		}
		// In each case we need to (re)trace the core. I.e. retracing if the empty
		// clause was already derived in an earlier minimization try
		LOG ("Tracing clausal core...");
		kitten_traverse_core_clauses (citten, &mini_pcs, get_final_from_core_with_bumping);
		stats.allrpr.kittencalls++;
		STOP (allrprsolve);
	}

	// Lightweight version of allrpr_kitten_catch_rat. Used for the first k tries
	// at minimization, before finally the LRAT chain is also extracted
	//  
	void Internal::allrpr_kitten_attempt_minimize (allrpr_mini_pcs &mini_pcs, const int attempt, const bool shuffle) {
		START (allrprsolve);
		assert (citten);

		#ifndef LOGGING
		(void) attempt;
		#endif
		LOG (clause, "Kitten Minimization Attempt %d on", attempt);

		for (const auto &lit: clause) {
			LOG ("Assuming %d", -lit);
			kitten_assume_signed (citten, -lit);
		}
		if (shuffle)
			kitten_shuffle_assumptions (citten);
		kitten_solve (citten);
		kitten_compute_clausal_core (citten, nullptr);
		kitten_traverse_core_clauses (citten, &mini_pcs, get_final_from_core);

		STOP (allrprsolve);
	}

	// attempt k rounds of minimization
	void Internal::allrpr_attempt_minimize_k_times (
		int &uip, allrpr_mini_pcs &mini_pcs, vector<int> &final, int &mini_again) {
		bool shuffle = true;
		for (int i = 0; i < opts.allrprretries; i++) {
      if (clause.size () == 0)
        break;
      if (opts.allrprreport) {
      	printf ("clause: ");
      	for (const int &lit : clause) {
      		printf ("%d ", lit);
      	}
      	printf ("\n");	
      }

      allrpr_kitten_attempt_minimize (mini_pcs, i, shuffle);
      LOG (mini_pcs.final_clause, "clause after attempt %i:", i);
      if (mini_pcs.final_clause.size () < clause.size ()) { // successful further further
        mini_again++;
        LOG (mini_pcs.final_clause, "%d minimized %s to", mini_again, mini_again > 0 ? "again" : "for the first time");
        if (opts.allrprreport) {
          printf ("KIT minimized in round %d\n", i);
        	printf ("KIT final size: %zu\n", mini_pcs.final_clause.size ());
        }
      }
      if (!final.empty ()) {
      	const int old_size = (int) clause.size ();
      	clause = mini_pcs.final_clause;
      	if (opts.allrprreorder && old_size > (int) final.size ()) {
      		LOG ("Reorder clause...");
      		minimize_sort_clause ();
      		reverse (clause.begin (), clause.end ());
      		shuffle = false;
      	} else 
      		shuffle = true;
      }
      else { // UNSAT, derived empty clause. allrpr_kitten_catch_rat will now just retrace core
        uip = 0;
        break;
      }
    }
	}

	// Updates potentially changed glue value and glue related statistics
	//
	void Internal::allrpr_update_glue (int uip, int& glue) {
		const int old_glue = glue;
		glue = 0;
		int lowest_level = var (uip).level;
		for (const int &lit : clause) { // clause is sorted by trail rank
			if (var (lit).level < lowest_level) {
				lowest_level = var (lit).level;
				glue++;
			}
		}
		const int improvement = old_glue - glue;
		if (improvement) {
			LOG ("glue improved by %d from %d to %d", improvement, old_glue, glue);
			stats.allrpr.nimprovedglue++;
			stats.allrpr.simprovedglue += improvement;

			const bool was_tier1 = old_glue <= tier1[false];
			const bool was_tier2 = old_glue <= tier2[false];
			if (!was_tier1 && glue <= tier1[false]) {
				LOG ("clause lifted to tier 1");
				stats.allrpr.liftedtier1++;
			}
			else if (!was_tier2 && glue <= tier2[false]) {
				LOG ("clause lifted to tier 2");
				stats.allrpr.liftedtier2++;
			}
		}
	}



}	