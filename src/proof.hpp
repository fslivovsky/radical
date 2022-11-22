#ifndef _proof_h_INCLUDED
#define _proof_h_INCLUDED

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

class File;
struct Clause;
struct Internal;
class Observer;

/*------------------------------------------------------------------------*/

// Provides proof checking and writing through observers.

class Proof {

  Internal * internal;

  vector<int> clause;           // of external literals
  uint64_t clause_id;            // id of added clause
  vector<Observer *> observers; // owned, so deleted in destructor

  void add_literal (int internal_lit);  // add to 'clause'
  void add_literals (Clause *);         // add to 'clause'

  void add_literals (const vector<int> &);      // ditto

  void add_original_clause ();  // notify observers of original clauses
  void add_derived_clause ();   // notify observers of derived clauses
  void delete_clause ();        // notify observers of deleted clauses

public:

  Proof (Internal *);
  ~Proof ();

  void connect (Observer * v) { observers.push_back (v); }

  // Add original clauses to the proof (for online proof checking).
  //
  void add_original_clause (uint64_t, const vector<int> &);

  // Add derived (such as learned) clauses to the proof.
  //
  void add_derived_empty_clause (uint64_t);
  void add_derived_unit_clause (uint64_t, int unit);
  void add_derived_clause (Clause *);
  void add_derived_clause (uint64_t, const vector<int> &);

  void delete_clause (uint64_t, const vector<int> &);
  void delete_clause (Clause *);

  // These two actually pretend to add and remove a clause.
  //
  void flush_clause (Clause *);           // remove falsified literals
  void strengthen_clause (Clause *, int); // remove second argument

  void flush ();
};

}

#endif
