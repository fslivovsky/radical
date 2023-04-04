#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// Provide eager backward subsumption for resolved clauses.

// The eliminator maintains a queue of clauses that are new and have to be
// checked to subsume or strengthen other (longer or same size) clauses.

void Eliminator::enqueue (Clause * c) {
  if (!internal->opts.elimbackward) return;
  if (c->enqueued) return;
  LOG (c, "backward enqueue");
  backward.push (c);
  c->enqueued = true;
}

Clause * Eliminator::dequeue () {
  if (backward.empty ()) return 0;
  Clause * res = backward.front ();
  backward.pop ();
  assert (res->enqueued);
  res->enqueued = false;
  LOG (res, "backward dequeue");
  return res;
}

Eliminator::~Eliminator () {
  while (dequeue ())
    ;
}

/*------------------------------------------------------------------------*/

void Internal::elim_backward_clause (Eliminator & eliminator, Clause *c) {
  assert (opts.elimbackward);
  assert (!c->redundant);
  if (c->garbage) return;
  LOG (c, "attempting backward subsumption and strengthening with");
  size_t len = UINT_MAX;
  unsigned size = 0;
  int best = 0;
  bool satisfied = false;
  assert (mini_chain.empty ());
  for (const auto & lit : *c) {
    const signed char tmp = val (lit);
    if (tmp > 0) { satisfied = true; break; }
    if (tmp < 0) {
      if (!opts.lrat || opts.lratexternal) continue;
      Flags & f = flags (lit);
      assert (!f.seen);                // sanity check
      if (f.seen) continue;
      f.seen = true;
      analyzed.push_back (lit);
      const unsigned uidx = vlit (-lit);
      uint64_t id = unit_clauses[uidx];
      assert (id);
      mini_chain.push_back (id);
      continue;
    }
    size_t l = occs (lit).size ();
    LOG ("literal %d occurs %zd times", lit, l);
    if (l < len) best = lit, len = l;
    mark (lit);
    size++;
  }
  if (satisfied) {
    LOG ("clause actually already satisfied");
    elim_update_removed_clause (eliminator, c);
    mark_garbage (c);
  } else if (len > (size_t) opts.elimocclim) {
    LOG ("skipping backward subsumption due to too many occurrences");
  } else {
    assert (len);
    LOG ("literal %d has smallest number of occurrences %zd", best, len);
    LOG ("marked %d literals in clause of size %d", size, c->size);
    for (auto & d : occs (best)) {
      if (d == c) continue;
      if (d->garbage) continue;
      if ((unsigned) d->size < size) continue;
      int negated = 0;
      unsigned found = 0;
      for (const auto & lit : *d) {
        signed char tmp = val (lit);
        if (tmp > 0) { satisfied = true; break; }
        if (tmp < 0) continue;
        tmp = marked (lit);
        if (!tmp) continue;
        if (tmp < 0) {
          if (negated) { size = UINT_MAX; break; }
          else negated = lit;
        }
        if (++found == size) break;
      }
      if (satisfied) {
        LOG (d, "found satisfied clause");
        elim_update_removed_clause (eliminator, d);
        mark_garbage (d);
      } else if (found == size) {
        if (!negated) {
          LOG (d, "found subsumed clause");
          elim_update_removed_clause (eliminator, d);
          mark_garbage (d);
          stats.subsumed++;
          stats.elimbwsub++;
        } else {
          int unit = 0;
          for (const auto & lit : * d) {
            const signed char tmp = val (lit);
            if (tmp < 0) {
              if (!opts.lrat || opts.lratexternal) continue;
              Flags & f = flags (lit);
              if (f.seen) continue;
              const unsigned uidx = vlit (-lit);
              uint64_t id = unit_clauses[uidx];
              assert (id);
              lrat_chain.push_back (id);
              continue;
            }
            if (tmp > 0) { satisfied = true; break; }
            if (lit == negated) continue;
            if (unit) { unit = INT_MIN; break; }
            else unit = lit;
          }
          if (opts.lrat && !opts.lratexternal) {
            // if (unit && unit != INT_MIN) {    // seems to introduce a bug
            for (auto p : mini_chain) {
              lrat_chain.push_back (p);
            }
            // }
            lrat_chain.push_back (d->id);
            lrat_chain.push_back (c->id);
          }
          assert (unit);
          if (satisfied) {
            mark_garbage (d);
            elim_update_removed_clause (eliminator, d);
          } else if (unit && unit != INT_MIN) {
            assert (unit);
            LOG (d, "unit %d through hyper unary resolution with", unit);
            assign_unit (unit);
            elim_propagate (eliminator, unit);
            break;
          } else if (occs (negated).size () <= (size_t) opts.elimocclim) {
            strengthen_clause (d, negated);
            remove_occs (occs (negated), d);
            elim_update_removed_lit (eliminator, negated);
            stats.elimbwstr++;
            assert (negated != best);
            eliminator.enqueue (d);
          }
          lrat_chain.clear ();
        }
      }
    }
  }
  clear_analyzed_literals ();
  mini_chain.clear ();
  unmark (c);
}

/*------------------------------------------------------------------------*/

void Internal::elim_backward_clauses (Eliminator & eliminator) {
  if (!opts.elimbackward) {
    assert (eliminator.backward.empty ());
    return;
  }
  START (backward);
  LOG ("attempting backward subsumption and strengthening with %zd clauses",
    eliminator.backward.size ());
  Clause * c;
  while (!unsat && (c = eliminator.dequeue ()))
    elim_backward_clause (eliminator, c);
  STOP (backward);
}

/*------------------------------------------------------------------------*/

}
