#include "internal.hpp"

namespace CaDiCaL {


void Internal::decompose_analyze_binary_chain (DFS * dfs, int from) {
  if (!opts.lrat || opts.lratexternal) return;
  LOG ("binary chain starting at %d", from);
  DFS & from_dfs = dfs[vlit (from)];
  Clause * reason = from_dfs.parent;
  /*
  if (val (from) > 0) {
    const unsigned uidx = vlit (from);
    uint64_t id = unit_clauses[uidx];
    assert (id);
    mini_chain.push_back (id);
    return;
  }
  */
  if (!reason) return;
  assert (reason->size == 2);
  mini_chain.push_back (reason->id);
  int other = reason->literals[0];
  other = other == from ? -reason->literals[1] : -other;
  Flags & f = flags (other);
  if (f.seen) return;
  f.seen = true;
  analyzed.push_back (other);
  decompose_analyze_binary_chain (dfs, other);
}

vector<Clause*> Internal::decompose_analyze_binary_clauses (DFS * dfs, int from) {
  vector<Clause * > result;
  LOG ("binary chain starting at %d", from);
  DFS & from_dfs = dfs[vlit (from)];
  Clause * reason = from_dfs.parent;
  while (reason) {
    result.push_back (reason);
    assert (reason->size == 2);
    int other = reason->literals[0];
    other = other == from ? -reason->literals[1] : -other;
    Flags & f = flags (other);
    if (f.seen) break;
    f.seen = true;
    analyzed.push_back (other);
    from = other;
    DFS & from_dfs = dfs[vlit (from)];
    reason = from_dfs.parent;
  }
  return result;
}


void Internal::decompose_conflicting_scc_lrat (DFS * dfs, vector<int> & scc) {
  if (!opts.lrat || opts.lratexternal) return;
  assert (lrat_chain.empty ());
  assert (mini_chain.empty ());
  for (auto & lit : scc) {
    Flags & f = flags (lit);
    if (f.seen) return;
    f.seen = true;
    analyzed.push_back (lit);
    decompose_analyze_binary_chain (dfs, lit);
    for (auto p = mini_chain.rbegin (); p < mini_chain.rend (); p++) {
      lrat_chain.push_back (*p);
    }
    /*
    if (back)
      for (auto p = mini_chain.rbegin (); p < mini_chain.rend (); p++) {
        lrat_chain.push_back (*p);
      }
    else 
      for (auto p : mini_chain) {
        lrat_chain.push_back (p);
      }
      */
    mini_chain.clear ();
  }
  clear_analyzed_literals ();
}

void Internal::clear_decomposed_literals () {
  LOG ("clearing %zd decomposed literals", decomposed.size ());
  for (const auto & lit : decomposed) {
    assert (marked_decompose (lit));
    unmark_decompose (lit);
  }
  decomposed.clear ();
}

// compute lrat_chain from a given starting reason to root
//
void Internal::decompose_analyze_lrat (DFS * dfs, Clause * reason) {
  if (!opts.lrat || opts.lratexternal) return;
  assert (lrat_chain.empty ());
  assert (reason);            // not sure yet.
  LOG (reason, "decompose analyze for");
  for (const auto lit : *reason) {
    const auto other = -lit;
    Flags & f = flags (other);
    if (f.seen) continue;
    f.seen = true;
    analyzed.push_back (other);
    if (val (other) > 0) {
      const unsigned uidx = vlit (other);
      uint64_t id = unit_clauses[uidx];
      assert (id);
      lrat_chain.push_back (id);
      continue;
    }
    assert (mini_chain.empty ());
    decompose_analyze_binary_chain (dfs, other);
    for (auto p = mini_chain.rbegin (); p < mini_chain.rend (); p++) {
      lrat_chain.push_back (*p);
    }
    mini_chain.clear ();
  }
  lrat_chain.push_back (reason->id);
  clear_analyzed_literals ();
}


// This performs one round of Tarjan's algorithm, e.g., equivalent literal
// detection and substitution, on the whole formula.  We might want to
// repeat it since its application might produce new binary clauses or
// units.  Such units might even result in an empty clause.

bool Internal::decompose_round () {

  if (!opts.decompose) return false;
  if (unsat) return false;
  if (terminated_asynchronously ()) return false;

  assert (!level);

  START_SIMPLIFIER (decompose, DECOMP);

  stats.decompositions++;

  const size_t size_dfs = 2*(1 + (size_t) max_var);
  DFS * dfs = new DFS[size_dfs];
  int * reprs = new int[size_dfs];
  clear_n (reprs, size_dfs);
  vector<vector<Clause*>> dfs_chains;
  dfs_chains.resize (size_dfs);
  if (opts.lrat && ! opts.lratexternal) {
    for (size_t i = 0; i > size_dfs; i++) {
      vector<Clause*> empty;
      dfs_chains[i] = empty;
    }
  }

  int non_trivial_sccs = 0, substituted = 0;
#ifndef QUIET
  int before = active ();
#endif
  unsigned dfs_idx = 0;

  vector<int> work;                     // depth first search working stack
  vector<int> scc;                      // collects members of one SCC

  // The binary implication graph might have disconnected components and
  // thus we have in general to start several depth first searches.

  for (auto root_idx : vars) {
    if (unsat) break;
    if (!active (root_idx)) continue;
    for (int root_sign = -1; !unsat && root_sign <= 1; root_sign += 2) {
      int root = root_sign * root_idx;
      if (dfs[vlit (root)].min == TRAVERSED) continue;  // skip traversed
      LOG ("new dfs search starting at root %d", root);
      assert (work.empty ());
      assert (scc.empty ());
      work.push_back (root);
      while (!unsat && !work.empty ()) {
        int parent = work.back ();
        DFS & parent_dfs = dfs[vlit (parent)];
        if (parent_dfs.min == TRAVERSED) {              // skip traversed
          assert (reprs [vlit (parent)]);
          work.pop_back ();
        } else {
          assert (!reprs [vlit (parent)]);

          // Go over all implied literals, thus need to iterate over all
          // binary watched clauses with the negation of 'parent'.

          Watches & ws = watches (-parent);

          // Two cases: Either the node has never been visited before, i.e.,
          // it's depth first search index is zero, then perform the
          // 'pre-fix' work before visiting it's children.  Otherwise all
          // it's children and nodes reachable from those children have been
          // visited and their minimum reachable depth first search index
          // has been computed.  This second case is the 'post-fix' work.

          if (parent_dfs.idx) {                         // post-fix

            work.pop_back ();                           // 'parent' done

            // Get the minimum reachable depth first search index reachable
            // from the children of 'parent'.

            unsigned new_min = parent_dfs.min;

            for (const auto & w : ws) {
              if (!w.binary ()) continue;
              const int child = w.blit;
              if (!active (child)) continue;
              DFS & child_dfs = dfs[vlit (child)];
              if (new_min > child_dfs.min) new_min = child_dfs.min;
            }

            LOG ("post-fix work dfs search %d index %u reaches minimum %u",
              parent, parent_dfs.idx, new_min);

            if (parent_dfs.idx == new_min) {            // entry to SCC

              // All nodes on the 'scc' stack after and including 'parent'
              // are in the same SCC.  Their representative is computed as
              // the smallest literal (index-wise) in the SCC.  If the SCC
              // contains both a literal and its negation, then the formula
              // becomes unsatisfiable.
              
              if (opts.lrat && !opts.lratexternal) {
                assert (analyzed.empty ());
                int other, first = 0;
                bool conflicting = false;
                size_t j = scc.size ();
                do {
                  assert (j > 0);
                  other = scc[--j];
                  if (!first || vlit (other) < vlit (first)) first = other;
                  Flags & f = flags (other);
                  if (other == -parent) {
                    conflicting = true;      // conflicting scc
                  }
                  if (f.seen) {
                    continue;                 // also conflicting scc
                  }
                  f.seen = true;
                  analyzed.push_back (other);
                } while (other != parent);
                
                assert (!conflicting || first > 0);
                vector<int> todo;
                if (conflicting) {
                  LOG ("conflicting scc simulating up at %d", parent);
                  todo.push_back (-parent);
                }
                else
                  todo.push_back (first);
                while (!todo.empty ()) {
                  const int next = todo.back ();
                  todo.pop_back ();
                  Watches & next_ws = watches (-next);
                  for (const auto & w : next_ws) {
                    if (!w.binary ()) continue;
                    const int child = w.blit;
                    if (!active (child)) continue;
                    if (!flags (child).seen) continue;
                    DFS & child_dfs = dfs[vlit (child)];
                    if (child_dfs.parent) continue;
                    child_dfs.parent = w.clause;
                    todo.push_back (child);
                  }
                }
                
                clear_analyzed_literals ();
              }

              int other, size = 0, repr = parent;
              assert (!scc.empty ());
              size_t j = scc.size ();
              do {
                assert (j > 0);
                other = scc[--j];
                if (other == -parent) {
                  LOG ("both %d and %d in one SCC", parent, -parent);
                  if (opts.lrat && !opts.lratexternal) {
                    Flags & f = flags (-parent);
                    f.seen = true;
                    analyzed.push_back (-parent);
                    decompose_analyze_binary_chain (dfs, parent);
                    for (auto p : mini_chain)
                      lrat_chain.push_back (p);
                    mini_chain.clear ();
                  }
                  assign_unit (parent);
                  if (opts.lrat && !opts.lratexternal) {
                    // bool ok = propagate ();                  // TODO differentiate between
                    propagate ();                               // normal usage and logging/debugging
                    // assert (!ok);                            // to avoid compiler warnings
                  }
                  learn_empty_clause ();
                  lrat_chain.clear ();
                } else {
                  if (abs (other) < abs (repr)) repr = other;
                  size++;
                }
              } while (!unsat && other != parent);

              if (unsat) break;

              LOG ("SCC of representative %d of size %d", repr, size);

              do {
                assert (!scc.empty ());
                other = scc.back ();
                scc.pop_back ();
                dfs[vlit (other)].min = TRAVERSED;
                if (frozen (other)) {
                  reprs[vlit (other) ] = other;
                  continue;
                }
                reprs[vlit (other)] = repr;
                if (other == repr) continue;
                substituted++;
                LOG ("literal %d in SCC of %d", other, repr);
                if (!opts.lrat || opts.lratexternal) continue;
                assert (mini_chain.empty ());
                Flags & f = flags (repr);
                f.seen = true;
                analyzed.push_back (repr);
                dfs_chains[vlit (other)] = decompose_analyze_binary_clauses (dfs, other);
                //reverse (dfs_chains[vlit (other)].begin (), dfs_chains[vlit (other)].end ());
                clear_analyzed_literals ();
              } while (other != parent);

              if (size > 1) non_trivial_sccs++;

            } else {

              // Current node 'parent' is in a non-trivial SCC but is not
              // the entry point of the SCC in this depth first search, so
              // keep it on the SCC stack until the entry point is reached.

              parent_dfs.min = new_min;
            }

          } else {                                      // pre-fix

            dfs_idx++;
            assert (dfs_idx < TRAVERSED);
            parent_dfs.idx = parent_dfs.min = dfs_idx;
            scc.push_back (parent);

            LOG ("pre-fix work dfs search %d index %u", parent, dfs_idx);

            // Now traverse all the children in the binary implication
            // graph but keep 'parent' on the stack for 'post-fix' work.

            for (const auto & w : ws) {
              if (!w.binary ()) continue;
              const int child = w.blit;
              if (!active (child)) continue;
              DFS & child_dfs = dfs[vlit (child)];
              if (child_dfs.idx) continue;
              work.push_back (child);
            }
          }
        }
      }
    }
  }

  erase_vector (work);
  erase_vector (scc);
  // delete [] dfs; need to postpone until after changing clauses...

  // Only keep the representatives 'repr' mapping.

  PHASE ("decompose",
    stats.decompositions,
    "%d non-trivial sccs, %d substituted %.2f%%",
    non_trivial_sccs, substituted, percent (substituted, before));

  bool new_unit = false, new_binary_clause = false;

  vector<Clause*> postponed_garbage;

  // Now go over all clauses and find clause which contain literals that
  // should be substituted by their representative.

  size_t clauses_size = clauses.size (), garbage = 0, replaced = 0;
  for (size_t i = 0; substituted && !unsat && i < clauses_size; i++) {
    Clause * c = clauses[i];
    if (c->garbage) continue;
    int j, size = c->size;
    for (j = 0; j < size; j++) {
      const int lit = c->literals[j];
      if (reprs [ vlit (lit) ] != lit) break;
    }

    if (j == size) continue;

    replaced++;
    LOG (c, "first substituted literal %d in", substituted);

    // Now copy the result to 'clause'.  Substitute literals if they have a
    // different representative.  Skip duplicates and false literals.  If a
    // literal occurs in both phases or is assigned to true the clause is
    // satisfied and can be marked as garbage.
    // if repr(-a) is in the new clause for some literal a in the clause
    // then the clause is subsumed by a (possibly transitive) binary clause
    // in this case we delete the clause and only learn the binary clause
    // if it was irredundant.

    assert (clause.empty ());
    assert (lrat_chain.empty ());
    assert (analyzed.empty ());
    bool satisfied = false;
    
    for (int k = 0; !satisfied && k < size; k++) {
      const int lit = c->literals[k];
      LOG (c, "looking at %d in ", lit);
      signed char tmp = val (lit);
      if (tmp > 0) {
        LOG ("satisfied");
        satisfied = true;
      }
      else if (tmp < 0) continue;
      else {
        const int other = reprs [vlit (lit)];
        LOG ("replaceable by %d", other);
        tmp = val (other);
        if (tmp < 0) continue;
        else if (tmp > 0) satisfied = true;
        else {
          tmp = marked (other);
          if (tmp < 0) satisfied = true;
          else if (!tmp) {
            mark (other);
            clause.push_back (other);
          }
        }
      }
    }
    // build lrat
    if (opts.lrat && !opts.lratexternal) {
      LOG ("building chain for not subsumed clause");
      assert (lrat_chain.empty ());
      assert (decomposed.empty ());
      for (const auto lit : *c) {          // build chain for each replaced literal
        auto other = -lit;
        if (val (other) > 0) {
          if (marked_decompose (other)) continue;
          mark_decomposed (other);
          const unsigned uidx = vlit (other);
          uint64_t id = unit_clauses[uidx];
          assert (id);
          lrat_chain.push_back (id);
          continue;
        }
        assert (mini_chain.empty ());
        for (auto p : dfs_chains[vlit (other)]) {
          if (marked_decompose (other)) continue;
          mark_decomposed (other);
          int implied = p->literals[0];
          implied = implied == other ? -p->literals[1] : -implied;
          LOG ("ADDED %d -> %d (%" PRIu64 ")", implied, other, p->id);
          other = implied;
          mini_chain.push_back (p->id);
          if (val (implied) <= 0) continue;
          if (marked_decompose (implied)) break;
          mark_decomposed (implied);
          // if (val (implied) == 0) continue;
          const unsigned uidx = vlit (implied);
          uint64_t id = unit_clauses[uidx];
          assert (id);
          mini_chain.push_back (id);
          break;
        }
        for (auto p = mini_chain.rbegin (); p != mini_chain.rend (); p++)
          lrat_chain.push_back (*p);
        mini_chain.clear ();
      }
      //clear_analyzed_literals ();
      clear_decomposed_literals ();
      lrat_chain.push_back (c->id);
      LOG (lrat_chain, "lrat_chain: ");
    }
    if (satisfied) {
      LOG (c, "satisfied after substitution (postponed)");
      postponed_garbage.push_back (c);
      garbage++;
    } else if (!clause.size ()) {
      LOG ("learned empty clause during decompose");
      learn_empty_clause ();
    } else if (clause.size () == 1) {
      LOG (c, "unit %d after substitution", clause[0]);
      assign_unit (clause[0]);
      mark_garbage (c);
      new_unit = true;
      garbage++;
    } else if (c->literals[0] != clause[0] ||
               c->literals[1] != clause[1]) {
      LOG ("need new clause since at least one watched literal changed");
      if (clause.size () == 2) new_binary_clause = true;
      size_t d_clause_idx = clauses.size ();
      Clause * d = new_clause_as (c);
      assert (clauses[d_clause_idx] == d);
      clauses[d_clause_idx] = c;
      clauses[i] = d;
      mark_garbage (c);
      garbage++;
    } else {
      LOG ("simply shrinking clause since watches did not change");
      assert (c->size > 2);
      if (!c->redundant) mark_removed (c);
      if (proof) {
        if (opts.lrat && !opts.lratexternal)
          proof->add_derived_clause (++clause_id, clause, lrat_chain);
        else                                              
          proof->add_derived_clause (++clause_id, clause);                          
        proof->delete_clause (c);
        c->id = clause_id;
      }
      size_t l;
      for (l = 2; l < clause.size (); l++)
        c->literals[l] = clause[l];
      int flushed = c->size - (int) l;
      if (flushed) {
        if (l == 2) new_binary_clause = true;
        LOG ("flushed %d literals", flushed);
        (void) shrink_clause (c, l);
      } else if (likely_to_be_kept_clause (c)) mark_added (c);
      LOG (c, "substituted");
    }
    while (!clause.empty ()) {
      int lit = clause.back ();
      clause.pop_back ();
      assert (marked (lit) > 0);
      unmark (lit);
    }
    lrat_chain.clear ();
  }

  if (!unsat && !postponed_garbage.empty ()) {
    LOG ("now marking %zd postponed garbage clauses",
      postponed_garbage.size ());
    for (const auto & c : postponed_garbage)
      mark_garbage (c);
  }
  erase_vector (postponed_garbage);

  PHASE ("decompose",
    stats.decompositions,
    "%zd clauses replaced %.2f%% producing %zd garbage clauses %.2f%%",
    replaced, percent (replaced, clauses_size),
    garbage, percent (garbage, replaced));

  erase_vector (scc);

  // Propagate found units.

  if (!unsat && propagated < trail.size () && !propagate ()) {
    LOG ("empty clause after propagating units from substitution");
    learn_empty_clause ();
  }

  // Finally, mark substituted literals as such and push the equivalences of
  // the substituted literals to their representative on the extension
  // stack to fix an assignment during 'extend'.
  //
  // TODO instead of adding the clauses to the extension stack one could
  // also just simply use the 'e2i' map as a union find data structure.
  // This would avoid the need to restore these clauses.

  for (auto idx : vars) {
    if (unsat) break;
    if (!active (idx)) continue;
    int other = reprs [ vlit (idx) ];
    if (other == idx) continue;
    assert (!flags (other).eliminated ());
    assert (!flags (other).substituted ());
    if (!flags (other).fixed ()) mark_substituted (idx);
    external->push_binary_clause_on_extension_stack (-idx, other);
    external->push_binary_clause_on_extension_stack (idx, -other);
  }

  delete [] reprs;
  delete [] dfs;
  erase_vector (dfs_chains);
  
  flush_all_occs_and_watches ();  // particularly the 'blit's

  bool success = unsat ||
    (substituted > 0 && (new_unit || new_binary_clause));
  report ('d', !opts.reportall && !success);

  STOP_SIMPLIFIER (decompose, DECOMP);

  return success;
}

void Internal::decompose () {
  for (int round = 1; round <= opts.decomposerounds; round++)
    if (!decompose_round ())
      break;
}

}