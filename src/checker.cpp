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
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  num_clauses++;
  num_garbage++;
  return res;
}

CheckerClause * Checker::new_unit_clause () {
  const size_t size = simplified.size ();
  assert (size == 1);
  const size_t bytes = sizeof (CheckerClause);
  CheckerClause * res = (CheckerClause *) new char [bytes];
  res->next = 0;
  res->hash = last_hash;
  res->id = last_id;
  res->size = size;
  num_clauses++;
  res->literals[0] = simplified[0];
  return res;
}

CheckerClause * Checker::new_clause () {
  const size_t size = simplified.size ();
  assert (size > 1), assert (size <= UINT_MAX);
  const size_t bytes = sizeof (CheckerClause) + (size - 2) * sizeof (int);
  CheckerClause * res = (CheckerClause *) new char [bytes];
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
  watcher (literals[0]).push_back (CheckerWatch (literals[1], res));
  watcher (literals[1]).push_back (CheckerWatch (literals[0], res));

  return res;
}

void Checker::delete_clause (CheckerClause * c) {
  if (c->size) {
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
          c->size = 0;                    // mark as garbage
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
      if (w.clause->size) *j++ = w;
    }
    if (j == ws.end ()) continue;
    if (j == ws.begin ()) erase_vector (ws);
    else ws.resize (j - ws.begin ());
  }

  for (CheckerClause * c = garbage, * next; c; c = next)
    next = c->next, delete_clause (c);

  assert (!num_garbage);
  garbage = 0;
}

/*------------------------------------------------------------------------*/

Checker::Checker (Internal * i)
:
  internal (i),
  size_vars (0), vals (0),
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
    if (lit == -prev) taut = true;      // tautological clause
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

// This is a standard propagation routine without using blocking literals
// nor without saving the last replacement position.

// TODO: we can have the special case that clauses are unit or falsified while
// inserted check if this invalidates the current implementation of propagate.
bool Checker::propagate () {
  bool res = true;
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
      const int blit = w.blit;
      assert (blit != -lit);
      const signed char blit_val = val (blit);
      if (blit_val > 0) continue;
      const unsigned size = w.size;
      if (size == 2) {                          // not precise since
        if (!w.clause->size) continue;
        if (blit_val < 0) {
          res = false;                          // clause might be garbage
          conflict = w.clause;
        }
        else assign_reason (w.blit, w.clause);  // but still sound
      } else {
        assert (size > 2);
        CheckerClause * c = w.clause;
        if (!c->size) { j--; continue; }        // skip garbage clauses
        assert (size == c->size);
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
    justified[l2a (lit)] = true;                 // this makes sense
    todo_justify[l2a (lit)];              // why??? -> think about it
  }
  assert (conflict);
  int counter = 0;
  for (int * i = conflict->literals; i < conflict->literals + conflict->size; i++) {
    int lit = *i;
    todo_justify[l2a (lit)] = true;
    counter++;             // new todo_justify means counter increase
  }
  LOG (conflict->literals, conflict->literals + conflict->size,
    "CHECKER LRAT conflict with");
  proof_chain.push_back (conflict->id);  // build proof in reverse, i.e. starting with conflict
  for (auto i = trail.end () - 1; i >= trail.begin (); i--) {
    int lit = *i;
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
    counter--;         // one of the todo_justify lits justified
    CheckerClause * reason_clause = reasons[l2a (lit)];
    assert (reason_clause);
    assert (reason_clause->size);
    LOG (reason_clause->literals,
      reason_clause->literals + reason_clause->size,
      "CHECKER LRAT add");
    proof_chain.push_back (reason_clause->id);
    for (int * i = reason_clause->literals; i < reason_clause->literals + reason_clause->size; i++) {
      if (todo_justify[l2a (*i)]) {
        LOG ("CHECKER LRAT lit %d already marked", lit);
      }
      else if (justified[l2a (*i)]) {
        LOG ("CHECKER LRAT lit %d already justified", lit); // cant happen as is
      }
      else {
        LOG ("CHECKER LRAT need to justify new lit %d", lit);
        counter++;             // new todo_justify means counter increase
        todo_justify[l2a (*i)] = true;
      }
    }
  }
  assert (!counter);
  LOG (proof_chain, "CHECKER LRAT reversed proof:");
  std::vector<int64_t> proof_chain_reverse;
  for (auto p = proof_chain.end () - 1; p >= proof_chain.begin (); p--)
    proof_chain_reverse.push_back (*p);
  return proof_chain_reverse;
}
bool Checker::check_lrat () {
  // TODO: implement :)
  return true;
}

bool Checker::check_lrat_proof (vector<int64_t> proof_chain) {
  LOG (simplified, "CHECKER LRAT checking clause");
  LOG (proof_chain, "CHECKER LRAT with proof_chain:");

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
      LOG ("CHECKER LRAT proof contains unneccessary empty clause %ld", id);
      continue;
    }
    int unit = 0;
    for (int * i = c->literals; i < c->literals + c->size; i++) {
      int lit = * i;
      if (checked_lit (-lit)) continue;
      assert (!checked_lit (lit));          // we dont want satisfied clauses in our proof
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
      LOG ("CHECKER check succeded, clause falsified %ld", id);
      assert (proof_chain.back () == id);   // we dont want unneccessary long proofs
      break;                                // would also be regarded as bug here
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
  if (!size) {
    LOG ("CHECKER added and checked empty %s clause", type);
    inconsistent = true;
  } else if (size == 1) {
    int lit = c->literals[0];
    int value = val (lit);
    stats.units++;
    if (!value) {
      LOG ("CHECKER checked and assigned %s unit clause %d", type, lit);
      assign_reason (lit, c);
    } else if (value > 0) {
      LOG ("CHECKER checked and updated reason for %s unit clause %d", type, lit);
      unassign_reason (lit);
      assign_reason (lit, c);
    } else {
      LOG ("CHECKER added and checked falsified %s unit clause %d", type, lit);
      inconsistent = true;
    }
  }
  /* else {
    int unit = 0;
    const int * p = c->literals;
    for (unsigned i = 0; i < size; i++) {
      int lit = *(p + i);
      if (val (lit) > 0)
    }
  } */
  if (!inconsistent && !propagate ()) {
    LOG ("CHECKER inconsistent after adding %s clause and propagating", type);
    inconsistent = true;
  }
}

void Checker::add_original_clause (int64_t id, const vector<int> & c) {
  if (inconsistent) return;
  START (checking);
  LOG (c, "CHECKER addition of original clause");
  LOG ("CHECKER clause id %ld", id);
  stats.added++;
  stats.original++;
  import_clause (c);
  last_id = id;
  assert (id);
  if (tautological () && !internal->opts.checkprooflrat) {  // if clause is tautological
    LOG ("CHECKER ignoring satisfied original clause");     // we can ignore it in drat
  }                                                         // but not in lrat
  else add_clause ("original");
  simplified.clear ();
  unsimplified.clear ();
  STOP (checking);
}

void Checker::add_derived_clause (int64_t id, const vector<int> & c) {
  if (inconsistent) return;
  START (checking);
  LOG (c, "CHECKER addition of derived clause");
  LOG ("CHECKER clause id %ld", id);
  stats.added++;
  stats.derived++;
  import_clause (c);
  last_id = id;
  assert (id);
  if (tautological () && !opt_lrat) {  // if clause is tautological
    LOG ("CHECKER ignoring satisfied derived clause");      // we can ignore it in drat
  }                                                         // but not in lrat
  else {
    bool res = opt_lrat ? check_lrat () : check ();
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
  STOP (checking);
}

/*------------------------------------------------------------------------*/

void Checker::delete_clause (int64_t id, const vector<int> & c) {
  if (inconsistent) return;
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
        if (opt_lrat) {
          CheckerClause * reason = reasons[l2a (lit)];
          if (reason == d) {
            assert (val (lit));
            assert (!unit);
            unassign_reason (lit);
            unit = lit;
          }
        }
      }
      if (unit) propagate ();
      for (const auto & lit : simplified) mark (lit) = false;
      
      // Remove from hash table, mark as garbage, connect to garbage list.
      num_garbage++;
      assert (num_clauses);
      num_clauses--;
      *p = d->next;
      d->next = garbage;
      garbage = d;
      d->size = 0;
      // If there are enough garbage clauses collect them. only in drat, not lrat
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
