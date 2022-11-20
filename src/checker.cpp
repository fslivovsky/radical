#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

inline unsigned Checker::l2u (int lit) {
   assert (lit);
   assert (lit != INT_MIN);
   unsigned res = 2*(abs (lit) - 1);
   if (lit < 0) res++;
   return res;
}

inline unsigned Checker::l2a (int lit) {
   assert (lit);
   assert (lit != INT_MIN);
   unsigned res = abs (lit);
   return res;
}

inline signed char Checker::val (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  assert (abs (lit) < size_vars);
  assert (vals[lit] == -vals[-lit]);
  return vals[lit];
}

signed char & Checker::mark (int lit) {
  const unsigned u = l2u (lit);
  assert (u < marks.size ());
  return marks[u];
}

signed char & Checker::checked_lit (int lit) {
  const unsigned u = l2u (lit);
  assert (u < checked_lits.size ());
  return checked_lits[u];
}

inline CheckerWatcher & Checker::watcher (int lit) {
  const unsigned u = l2u (lit);
  assert (u < watchers.size ());
  return watchers[u];
}

/*------------------------------------------------------------------------*/
CheckerClause * Checker::new_empty_clause () {
  const size_t size = simplified.size ();
  assert (!size);
  const size_t bytes = sizeof (CheckerClause);
  CheckerClause * res = (CheckerClause *) new char [bytes];
  res->garbage = false;
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  num_clauses++;
  return res;
}

CheckerClause * Checker::new_unit_clause () {
  const size_t size = simplified.size ();
  assert (size == 1);
  const size_t bytes = sizeof (CheckerClause);
  CheckerClause * res = (CheckerClause *) new char [bytes];
  res->garbage = false;
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  num_clauses++;
  res->literals[0] = simplified[0];
  unit_clauses.push_back (res);
  return res;
}

CheckerClause * Checker::new_clause () {
  const size_t size = simplified.size ();
  assert (size > 1), assert (size <= UINT_MAX);
  const size_t bytes = sizeof (CheckerClause) + (size - 2) * sizeof (int);
  CheckerClause * res = (CheckerClause *) new char [bytes];
  res->garbage = false;
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  int * literals = res->literals, * p = literals;
  for (const auto & lit : simplified)
    *p++ = lit;
  num_clauses++;

  // First two literals are used as watches and should not be false.
  //
  for (unsigned i = 0; i < 2; i++) {
    int lit = literals[i];
    if (val (lit) >= 0) continue;
    for (unsigned j = i + 1; j < size; j++) {
      int other = literals[j];
      if (val (other) < 0) continue;
      swap (literals[i], literals[j]);
      break;
    }
  }
  // assert (val (literals [0]) >= 0);
  // assert (val (literals [1]) >= 0);
  // we cannot assert this here since we can add falsified clauses.
  // so we have to check for these cases in propagate
  if (!new_clause_taut) {
    watcher (literals[0]).push_back (CheckerWatch (literals[1], res));
    watcher (literals[1]).push_back (CheckerWatch (literals[0], res));
  } else { LOG ("CHECKER clause not added to watchers"); }
  return res;
}

void Checker::delete_clause (CheckerClause * c) {
  assert (c);
  if (!c->garbage) {
    assert (num_clauses);
    num_clauses--;
  } else {
    assert (num_garbage);
    num_garbage--;
  }
  delete [] (char*) c;
}

void Checker::enlarge_clauses () {
  assert (num_clauses == size_clauses);
  const uint64_t new_size_clauses = size_clauses ? 2*size_clauses : 1;
  LOG ("CHECKER enlarging clauses of checker from %" PRIu64 " to %" PRIu64,
    (uint64_t) size_clauses, (uint64_t) new_size_clauses);
  CheckerClause ** new_clauses;
  new_clauses = new CheckerClause * [ new_size_clauses ];
  clear_n (new_clauses, new_size_clauses);
  for (uint64_t i = 0; i < size_clauses; i++) {
    for (CheckerClause * c = clauses[i], * next; c; c = next) {
      next = c->next;
      const uint64_t h = reduce_hash (c->hash, new_size_clauses);
      c->next = new_clauses[h];
      new_clauses[h] = c;
    }
  }
  delete [] clauses;
  clauses = new_clauses;
  size_clauses = new_size_clauses;
}

bool Checker::clause_satisfied (CheckerClause * c) {
  for (unsigned i = 0; i < c->size; i++)
    if (val (c->literals[i]) > 0)
      return true;
  return false;
}

bool Checker::clause_falsified (CheckerClause * c) {
  for (unsigned i = 0; i < c->size; i++)
    if (val (c->literals[i]) >= 0)
      return false;
  return true;
}

// The main reason why we have an explicit garbage collection phase is that
// removing clauses from watcher lists eagerly might lead to an accumulated
// quadratic algorithm.  Thus we delay removing garbage clauses from watcher
// lists until garbage collection (even though we remove garbage clauses on
// the fly during propagation too).  We also remove satisfied clauses.
//
// Problem: this should only happen in drat not in lrat!! Done.
//
void Checker::collect_garbage_clauses () {

  stats.collections++;

  if (!opt_lrat) {
    for (size_t i = 0; i < size_clauses; i++) {
      CheckerClause ** p = clauses + i, * c;
      while ((c = *p)) {
        if (clause_satisfied (c)) {
          c->garbage = true;                    // mark as garbage
          *p = c->next;
          c->next = garbage;
          garbage = c;
          num_garbage++;
          assert (num_clauses);
          num_clauses--;
        } else p = &c->next;
      }
    }
  }

  LOG ("CHECKER collecting %" PRIu64 " garbage clauses %.0f%%",
    num_garbage, percent (num_garbage, num_clauses));

  for (int lit = -size_vars + 1; lit < size_vars; lit++) {
    if (!lit) continue;
    CheckerWatcher & ws = watcher (lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (;i != end; i++) {
      CheckerWatch & w = *i;
      if (!w.clause->garbage) *j++ = w;
    }
    if (j == ws.end ()) continue;
    if (j == ws.begin ()) erase_vector (ws);
    else ws.resize (j - ws.begin ());
  }

  auto end = inconsistent_clauses.end ();
  auto j = inconsistent_clauses.begin ();
  for (auto i = j; i != end; i++) {
    CheckerClause * c = *i;
    if (c->garbage) continue;            // garbage clause
    if (!clause_falsified (c)) continue;
    *j++ = c;
  }
  inconsistent_clauses.resize (j - inconsistent_clauses.begin ());
  end = unit_clauses.end ();
  j = unit_clauses.begin ();
  for (auto i = j; i != end; i++) {
    CheckerClause * c = *i;
    if (c->garbage) continue;            // garbage clause
    *j++ = c;
  }
  unit_clauses.resize (j - unit_clauses.begin ());

  for (CheckerClause * c = garbage, * next; c; c = next)
    next = c->next, delete_clause (c);

  assert (!num_garbage);
  garbage = 0;
}

/*------------------------------------------------------------------------*/

Checker::Checker (Internal * i)
:
  internal (i),
  size_vars (0), vals (0), new_clause_taut (0),
  inconsistent (false), opt_lrat (internal->opts.checkprooflrat),
  num_clauses (0), num_garbage (0), size_clauses (0), clauses (0), garbage (0),
  next_to_propagate (0), last_hash (0), last_id (0)
{
  LOG ("CHECKER new");
  assert (internal->opts.checkprooflrat == opt_lrat);
  // Initialize random number table for hash function.
  //
  Random random (42);
  for (unsigned n = 0; n < num_nonces; n++) {
    uint64_t nonce = random.next ();
    if (!(nonce & 1)) nonce++;
    assert (nonce), assert (nonce & 1);
    nonces[n] = nonce;
  }

  memset (&stats, 0, sizeof (stats));           // Initialize statistics.

  const size_t bytes = sizeof (CheckerClause);
  assumption = (CheckerClause *) new char [bytes];  // assumption clause
  assumption->garbage = false;
  assumption->next = 0;
  assumption->hash = 0;
  assumption->id = 0;
  assumption->size = 0;

}

Checker::~Checker () {
  LOG ("CHECKER delete");
  vals -= size_vars;
  delete [] vals;
  for (size_t i = 0; i < size_clauses; i++)
    for (CheckerClause * c = clauses[i], * next; c; c = next)
      next = c->next, delete_clause (c);
  for (CheckerClause * c = garbage, * next; c; c = next)
    next = c->next, delete_clause (c);
  delete [] clauses;
  num_clauses++;
  delete_clause (assumption);
}

/*------------------------------------------------------------------------*/

// The simplicity for accessing 'vals' and 'watchers' directly through a
// signed integer literal, comes with the price of slightly more complex
// code in deleting and enlarging the checker data structures.

void Checker::enlarge_vars (int64_t idx) {

  assert (0 < idx), assert (idx <= INT_MAX);

  int64_t new_size_vars = size_vars ? 2*size_vars : 2;
  while (idx >= new_size_vars) new_size_vars *= 2;
  LOG ("CHECKER enlarging variables of checker from %" PRId64 " to %" PRId64 "",
    size_vars, new_size_vars);

  signed char * new_vals;
  new_vals = new signed char [ 2*new_size_vars ];
  clear_n (new_vals, 2*new_size_vars);
  new_vals += new_size_vars;
  if (size_vars) // To make sanitizer happy (without '-O').
    memcpy ((void*) (new_vals - size_vars),
            (void*) (vals - size_vars), 2*size_vars);
  vals -= size_vars;
  delete [] vals;
  vals = new_vals;
  
  reasons.resize (new_size_vars);
  justified.resize (new_size_vars);
  todo_justify.resize (new_size_vars);
  for (int64_t i = size_vars; i < new_size_vars; i++)
  {
    reasons[i] = 0;
    justified[i] = 0;
    todo_justify[i] = 0;
  }
  
  watchers.resize (2*new_size_vars);
  marks.resize (2*new_size_vars);
  checked_lits.resize (2*new_size_vars);
  
  assert (idx < new_size_vars);
  size_vars = new_size_vars;
}

inline void Checker::import_literal (int lit) {
  assert (lit);
  assert (lit != INT_MIN);
  int idx = abs (lit);
  if (idx >= size_vars) enlarge_vars (idx);
  simplified.push_back (lit);
  unsimplified.push_back (lit);
}

void Checker::import_clause (const vector<int> & c) {
  for (const auto & lit : c)
    import_literal (lit);
}

struct lit_smaller {
  bool operator () (int a, int b) const {
    int c = abs (a), d = abs (b);
    if (c < d) return true;
    if (c > d) return false;
    return a < b;
  }
};

bool Checker::tautological () {
  sort (simplified.begin (), simplified.end (), lit_smaller ());
  const auto end = simplified.end ();
  auto j = simplified.begin ();
  int prev = 0;
  bool taut = false;
  for (auto i = j; i != end; i++) {
    int lit = *i;
    if (lit == prev) continue;          // duplicated literal
    if (lit == -prev) { taut = true; new_clause_taut = true; }  // tautological clause
    const signed char tmp = val (lit);
    if (tmp > 0) taut = true;           // satisfied literal and clause
    *j++ = prev = lit;
  }
  simplified.resize (j - simplified.begin ());
  return taut;
}

/*------------------------------------------------------------------------*/

uint64_t Checker::reduce_hash (uint64_t hash, uint64_t size) {
  assert (size > 0);
  unsigned shift = 32;
  uint64_t res = hash;
  while ((((uint64_t)1) << shift) > size) {
    res ^= res >> shift;
    shift >>= 1;
  }
  res &= size - 1;
  assert (res < size);
  return res;
}

uint64_t Checker::compute_hash (const int64_t id) {
  assert (id > 0);
  unsigned j = id % num_nonces;                 // dont know if this is a good
  uint64_t tmp = nonces[j] * (uint64_t) id;     // hash funktion or if it is
  return last_hash = tmp;                       // even better than just using id
}

CheckerClause ** Checker::find (const int64_t id) {
  stats.searches++;
  CheckerClause ** res, * c;
  const uint64_t hash = compute_hash (id);
  const uint64_t h = reduce_hash (hash, size_clauses);
  for (res = clauses + h; (c = *res); res = &c->next) {
    if (c->hash == hash && c->id == id) {
      break;
    }
    stats.collisions++;
  }
  return res;
}

CheckerClause * Checker::insert () {
  stats.insertions++;
  if (num_clauses == size_clauses) enlarge_clauses ();
  const uint64_t h = reduce_hash (compute_hash (last_id), size_clauses);
  CheckerClause * c;
  if (!simplified.size ()) c = new_empty_clause ();
  else if (simplified.size () == 1) c = new_unit_clause ();
  else c = new_clause ();
  c->next = clauses[h];
  clauses[h] = c;
  return c;
}

/*------------------------------------------------------------------------*/

inline void Checker::assign (int lit) {
  assert (!val (lit));   // cannot guarantee (!val (lit)) anymore :/ -> yes we can!
  vals[lit] = 1;
  vals[-lit] = -1;
  trail.push_back (lit);
}

inline void Checker::assume (int lit) {
  signed char tmp = val (lit);
  if (tmp > 0) return;
  assert (!tmp);
  reasons[l2a (lit)] = assumption;
  stats.assumptions++;
  assign (lit);
}

inline void Checker::assign_reason (int lit, CheckerClause * reason_clause) {
  assert (!opt_lrat || !reasons[l2a (lit)]);
  reasons[l2a (lit)] = reason_clause;
  assign (lit);
}

inline void Checker::unassign_reason (int lit) {
  assert (!opt_lrat || reasons[l2a (lit)]);
  reasons[l2a (lit)] = 0;
  assert (val (lit) > 0);
  assert (val (-lit) < 0);
  vals[lit] = vals[-lit] = 0;
}


void Checker::backtrack (unsigned previously_propagated) {

  assert (previously_propagated <= trail.size ());

  while (trail.size () > previously_propagated) {
    int lit = trail.back ();
    unassign_reason (lit);
    trail.pop_back ();
  }

  trail.resize (previously_propagated);
  next_to_propagate = previously_propagated;
  assert (trail.size () == next_to_propagate);
}

/*------------------------------------------------------------------------*/


bool Checker::unit_propagate () {
  const auto end = unit_clauses.end ();
  bool res = true;
  auto j = unit_clauses.begin (), i = j;
  for (; res && i != end; i++) {
    CheckerClause * c = *j++ = *i;
    if (c->garbage) { j--; continue; }        // skip garbage clauses
    const unsigned size = c->size;
    assert (size == 1);
    if (size == 1) {
      int lit = c->literals[0];
      int value = val (lit);
      if (value > 0) continue;
      else if (!value) assign_reason (c->literals[0], c);
      else {
        res = false;
        conflict = c;
      }
    }
  }
  while (i != end) *j++ = *i++;
  unit_clauses.resize (j - unit_clauses.begin ());
  return res;
}

// This is a standard propagation routine without using blocking literals
// nor without saving the last replacement position.
bool Checker::propagate () {
  bool res = unit_propagate ();
  while (res && next_to_propagate < trail.size ()) {
    int lit = trail[next_to_propagate++];
    stats.propagations++;
    assert (val (lit) > 0);
    assert (abs (lit) < size_vars);
    CheckerWatcher & ws = watcher (-lit);
    const auto end = ws.end ();
    auto j = ws.begin (), i = j;
    for (; res && i != end; i++) {
      CheckerWatch & w = *j++ = *i;
      if (w.clause->garbage) { j--; continue; }        // skip garbage clauses
      assert (w.size == w.clause->size);
      const int blit = w.blit;
      assert (blit != -lit);
      const signed char blit_val = val (blit);
      if (blit_val > 0) continue;
      const unsigned size = w.size;
      if (size == 1) {                                 // should not happen
        if (blit_val < 0) {
          res = false;
          conflict = w.clause;
        }
        else assign_reason (w.blit, w.clause);
      }
      else if (size == 2) {                          
        if (blit_val < 0) {
          res = false;
          conflict = w.clause;
        }
        else assign_reason (w.blit, w.clause); 
      } else {
        assert (size > 2);
        CheckerClause * c = w.clause;
        int * lits = c->literals;
        int other = lits[0]^lits[1]^(-lit);
        assert (other != -lit);
        signed char other_val = val (other);
        if (other_val > 0) { j[-1].blit = other; continue; }
        lits[0] = other, lits[1] = -lit;
        unsigned k;
        int replacement = 0;
        signed char replacement_val = -1;
        for (k = 2; k < size; k++)
          if ((replacement_val = val (replacement = lits[k])) >= 0)
            break;
        if (replacement_val >= 0) {
          watcher (replacement).push_back (CheckerWatch (-lit, c));
          swap (lits[1], lits[k]);
          j--;
        } else if (!other_val) assign_reason (other, c);
        else {
          res = false;
          conflict = c;
        }
      }
    }
    while (i != end) *j++ = *i++;
    ws.resize (j - ws.begin ());
  }
  return res;
}

vector<int64_t> Checker::build_lrat_proof () {
  LOG (simplified, "CHECKER LRAT building proof for");

  vector<int64_t> proof_chain;
  for (auto b : justified) b = false;
  for (auto b : todo_justify) b = false;
  for (const auto & lit : simplified) {
    if (val (lit) < 0)                             // TODO: find out how
      justified[l2a (lit)] = true;                 // this makes sense
  }                                                // and how to prevent
  int counter = 0;                                 // issues with unnecessarily long proofs
  for (int * i = conflict->literals; i < conflict->literals + conflict->size; i++) {
    int lit = *i;
    todo_justify[l2a (lit)] = true;
    counter++;             // new todo_justify means counter increase
  }
  proof_chain.push_back (conflict->id);  // build proof in reverse, i.e. starting with conflict
  for (auto p = trail.end () - 1; p >= trail.begin (); p--) {
    int lit = *p;
    if (!counter) break;    // invariant is that counter = number of active todo_justify
                            // this means we are done here
    if (!todo_justify [l2a (lit)]) {
      LOG ("CHECKER LRAT lit %d not needed", lit);
      continue;
    }
    if (justified [l2a (lit)]) {
      LOG ("CHECKER LRAT lit %d already justified", lit);
      counter--;       // one of the todo_justify lits justified
      continue;
    }
    justified [l2a (lit)] = true;
    LOG ("CHECKER LRAT justify lit %d", lit);
    counter--;         // one of the todo_justify lits justified
    CheckerClause * reason_clause = reasons[l2a (lit)];
    assert (reason_clause);
    assert (!reason_clause->garbage);
    proof_chain.push_back (reason_clause->id);
    const int * rp = reason_clause->literals;
    for (unsigned i = 0; i < reason_clause->size; i++) {
      int reason_lit = *(rp + i);
      if (todo_justify[l2a (reason_lit)]) {
        LOG ("CHECKER LRAT lit %d already marked", reason_lit);
      }
      else if (justified[l2a (reason_lit)]) {
        LOG ("CHECKER LRAT lit %d already justified", reason_lit);
      }
      else {
        LOG ("CHECKER LRAT need to justify new lit %d", reason_lit);
        counter++;             // new todo_justify means counter increase
        todo_justify[l2a (reason_lit)] = true;
      }
    }
  }
  assert (!counter);
  vector<int64_t> proof_chain_reverse;
  for (auto p = proof_chain.end () - 1; p >= proof_chain.begin (); p--)
    proof_chain_reverse.push_back (*p);
  return proof_chain_reverse;
}


bool Checker::check_lrat () {
  stats.checks++;
  unsigned previously_propagated = next_to_propagate;
  unsigned previous_trail_size = trail.size ();
  
  bool res = false;
  bool falsified = true;
  conflict = 0;
  for (const auto & lit : simplified)
  {
    if (val (lit) > 0) {
      res = true;
      falsified = false;
      conflict = reasons[l2a (lit)];
      LOG ("CHECKER LRAT check already satisfied clause");
    } else if (!val (lit)) {
      assume (-lit);
      falsified = false;
    }
  }

  if (falsified) {                            // if we add a falsified clause
    assert (inconsistent);                    // our internal state must already
    bool found_conflict = false;              // be inconsistent and we should
    for (auto & c : inconsistent_clauses) {   // have an inconsistent clause
      LOG ("CHECKER check clause id %ld inconsistent", c->id);
      LOG ("CHECKER garbage %d, falsified %d", c->garbage, clause_falsified (c));
      if (!c->garbage && clause_falsified (c)) {
        LOG ("CHECKER yes");
        found_conflict = true;
        conflict = c;
        break;
      }
      LOG ("CHECKER no");
    }
    assert (found_conflict);
    if (!found_conflict) {
      backtrack (previous_trail_size);
      next_to_propagate = previously_propagated;
      return false;
    }
    res = inconsistent;
  }
  else if (!res) res = !propagate ();
  assert(res && conflict);                                // TODO: bug. this fails.
  vector<int64_t> proof = build_lrat_proof ();
  backtrack (previous_trail_size);
  next_to_propagate = previously_propagated;

  // we backtrack first and then check to emphazise that checking should not
  // be  dependent on the internal state
  return check_lrat_proof (proof);
}


bool Checker::check_lrat_proof (vector<int64_t> proof_chain) {
  LOG (simplified, "CHECKER LRAT checking clause");

  assert (proof_chain.size ());
  for (auto & b : checked_lits) b = false;        // empty the vector
  for (const auto & lit : simplified) {          // initialize -lit=true for
    checked_lit (-lit) = true;                  // every lit in the learned clause
  }
  
  for (auto &id : proof_chain) {
    CheckerClause * c = * find (id);
    if (!c)
    {
      LOG ("CHECKER LRAT failed. Did not find clause with id %ld", id);
      return false;
    }
    if (!c->size) {
      LOG ("CHECKER LRAT proof contains unnecessary empty clause %ld", id);
      continue;
    }
    int unit = 0;
    for (int * i = c->literals; i < c->literals + c->size; i++) {
      int lit = * i;
      if (checked_lit (-lit)) continue;     // TODO:
      // assert (!checked_lit (lit));       // we dont want satisfied clauses in our proof
                                            // points to bug in proof building
                                            // i.e. clauses appearing multiple times
      if (unit) { unit = INT_MIN; break; }  // multiple unfalsified literals
      unit = lit;                           // potential unit
    }
    if (unit == INT_MIN) {
      LOG ("CHECKER check failed, found non unit clause %ld", id);
      return false;
    }
    if (!unit) {
      LOG ("CHECKER check succeded, clause falsified %ld", id);  // TODO:
      // assert (proof_chain.back () == id);   // we dont want unnecessary long proofs
      break;                                   // would also be regarded as bug here
    }
    LOG ("CHECKER found unit clause %ld, assign %d", id, unit);
    checked_lit (unit) = true;
  }
  return true;
}

bool Checker::check () {
  stats.checks++;
  if (inconsistent) return true;
  unsigned previously_propagated = next_to_propagate;
  for (const auto & lit : simplified)
  {
    assume (-lit);
  }
  bool res = !propagate ();
  backtrack (previously_propagated);
  return res;
}

/*------------------------------------------------------------------------*/

void Checker::add_clause (const char * type) {
#ifndef LOGGING
  (void) type;
#endif

  CheckerClause * c = insert ();

  const unsigned size = c->size;
  bool sat = clause_satisfied (c);
  int unit = 0;
  if (!sat) {
    const int * p = c->literals;
    for (unsigned i = 0; i < size; i++) {
      int lit = *(p + i);
      if (!val (lit)) {
        if (unit) { unit = INT_MIN; break; }
        unit = lit;
      }
    }
  }
  
  if (!size) {
    LOG ("CHECKER added and checked empty %s clause", type);
    LOG ("CHECKER clause with id %ld is now falsified", c->id);
    inconsistent = true;
    inconsistent_clauses.push_back (c);
  } else if (sat) {
    LOG ("CHECKER added and checked satisfied %s clause", type);
  } else if (!unit) {
    LOG ("CHECKER added and checked falsified %s clause with id %ld", type, c->id);    
    inconsistent = true;
    inconsistent_clauses.push_back (c);
  } else if (unit == INT_MIN) {
    LOG ("CHECKER added and checked non unit %s clause", type);    
  } else {
    stats.units++;
    LOG ("CHECKER checked and assigned %s unit clause %d", type, unit);
    assign_reason (unit, c);
    if (!propagate ()) {
      LOG ("CHECKER inconsistent after adding %s clause and propagating", type);
      LOG ("CHECKER clause with id %ld is now falsified", conflict->id);
      inconsistent = true;
      inconsistent_clauses.push_back (conflict);
      assert (clause_falsified (conflict));
    }
  }
  conflict = 0;
}

void Checker::add_original_clause (int64_t id, const vector<int> & c) {
  if (!opt_lrat && inconsistent) return;
  START (checking);
  LOG (c, "CHECKER addition of original clause");
  LOG ("CHECKER clause id %ld", id);
  stats.added++;
  stats.original++;
  import_clause (c);
  last_id = id;
  assert (id);
  assert (!new_clause_taut);
  if (tautological () && !opt_lrat) {  // if clause is tautological
    LOG ("CHECKER ignoring satisfied original clause");     // we can ignore it in drat
  }                                                         // but not in lrat
  else add_clause ("original");
  simplified.clear ();
  unsimplified.clear ();
  new_clause_taut = false;
  STOP (checking);
}

void Checker::add_derived_clause (int64_t id, const vector<int> & c) {
  if (!opt_lrat && inconsistent) return;
  START (checking);
  LOG (c, "CHECKER addition of derived clause");
  LOG ("CHECKER clause id %ld", id);
  stats.added++;
  stats.derived++;
  import_clause (c);
  last_id = id;
  assert (id);
  assert (!new_clause_taut);
  if (tautological () && !opt_lrat) {  // if clause is tautological
    LOG ("CHECKER ignoring satisfied derived clause");      // we can ignore it in drat
  }                                                         // but not in lrat
  else {
    bool res = new_clause_taut;
    if (!res) res = opt_lrat ? check_lrat () : check ();
    if (!res) {
    fatal_message_start ();
    fputs ("failed to check derived clause:\n", stderr);
    for (const auto & lit : unsimplified)
      fprintf (stderr, "%d ", lit);
    fputc ('0', stderr);
    fatal_message_end ();
    }
    else add_clause ("derived");
  }
  simplified.clear ();
  unsimplified.clear ();
  new_clause_taut = false;
  STOP (checking);
}

/*------------------------------------------------------------------------*/

void Checker::delete_clause (int64_t id, const vector<int> & c) {
  if (!opt_lrat && inconsistent) return;
  START (checking);
  LOG (c, "CHECKER checking deletion of clause");
  LOG ("CHECKER clause id %ld", id);
  stats.deleted++;
  import_clause (c);
  last_id = id;
  if (tautological () && !opt_lrat) {
    LOG ("CHECKER ignoring deletion of satisfied clause"); // we can ignore it in drat
  }
  else {
    CheckerClause ** p = find (id), * d = *p;
    if (d) {
      for (const auto & lit : simplified) mark (lit) = true;
      int unit = 0;
      const int * dp = d->literals;               // d should have the same literals
      for (unsigned i = 0; i < d->size; i++) {    // as simplified if the code is not buggy
        int lit = *(dp + i);
        assert (mark (lit));
        if (opt_lrat) {                           // we can ignore it in drat
          CheckerClause * reason = reasons[l2a (lit)];
          if (!val (lit)) LOG ("CHECKER skipping lit %d not assigned", lit);
          else LOG ("CHECKER lit %d reason id %ld", lit, reason->id);
          if (reason == d) {
            LOG ("CHECKER reason matches, unassigning lit %d", lit);
            assert (val (lit));
            assert (!unit);
            unit = lit;
          }
        }
      }
      for (const auto & lit : simplified) mark (lit) = false;
      
      // Remove from hash table, mark as garbage, connect to garbage list.
      num_garbage++;
      assert (num_clauses);
      num_clauses--;
      *p = d->next;
      d->next = garbage;
      garbage = d;
      d->garbage = true;

      if (unit) {
        LOG (trail.begin (), trail.end (), "CHECKER propagated lits before deletion");
        while (trail.size ()) {      // backtracking in trail until we hit
          int tlit = trail.back ();  // the right lit.
          if (tlit == unit) break;    // this is needed to make sure the
          unassign_reason (tlit);    // trail is always a topological order
          trail.pop_back ();         // for the reason graph
        }                            // alternatively we could ignore the
        assert (trail.size ());      // trail while building the lrat proof
        unassign_reason (unit);       // I don't know which is better or if
        trail.pop_back ();           // I missed some other solution.
        next_to_propagate = 0;      // trail.size (); was buggy because we need to propagate here
        bool res = propagate ();    // TODO: find out if this is the best solution
        LOG (trail.begin (), trail.end (), "CHECKER propagated lits after deletion");
        assert (res || inconsistent);            // result in a different state
        if (!res) {                              // TODO: maybe not guaranteed for
          inconsistent = true;                   // if there are no unit clauses
          inconsistent_clauses.push_back (conflict);
        }
      }
      
      // If there are enough garbage clauses collect them.
      if (num_garbage > 0.5 * max ((size_t) size_clauses, (size_t) size_vars))
        collect_garbage_clauses ();
    } else {
      fatal_message_start ();
      fputs ("deleted clause not in proof:\n", stderr);
      for (const auto & lit : unsimplified)
        fprintf (stderr, "%d ", lit);
      fputc ('0', stderr);
      fatal_message_end ();
    }
  }
  simplified.clear ();
  unsimplified.clear ();
  conflict = 0;
  new_clause_taut = false;
  STOP (checking);
}

/*------------------------------------------------------------------------*/

void Checker::dump () {
  int max_var = 0;
  for (uint64_t i = 0; i < size_clauses; i++)
    for (CheckerClause * c = clauses[i]; c; c = c->next)
      for (unsigned i = 0; i < c->size; i++)
        if (abs (c->literals[i]) > max_var)
          max_var = abs (c->literals[i]);
  printf ("p cnf %d %" PRIu64 "\n", max_var, num_clauses);
  for (uint64_t i = 0; i < size_clauses; i++)
    for (CheckerClause * c = clauses[i]; c; c = c->next) {
      for (unsigned i = 0; i < c->size; i++)
        printf ("%d ", c->literals[i]);
      printf ("0\n");
    }
}

}
