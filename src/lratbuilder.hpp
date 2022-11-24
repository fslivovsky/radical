#ifndef _lratbuilder_hpp_INCLUDED
#define _lratbuilder_hpp_INCLUDED

#include "observer.hpp"         // Alphabetically after 'lratbuilder'.

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This checker implements an online forward DRUP proof checker enabled by
// 'opts.checkproof' (requires 'opts.check' also to be enabled).  This is
// useful for model based testing (and delta-debugging), where we can not
// rely on an external proof checker such as 'drat-trim'.  We also do not
// have yet  a flow for offline incremental proof checking, while this
// checker here can also be used in an incremental setting.
//
// In essence the checker implements is a simple propagation online SAT
// solver with an additional hash table to find clauses fast for
// 'delete_clause'.  It requires its own data structure for clauses
// ('LratBuilderClause') and watches ('LratBuilderWatch').
//
// In our experiments the checker slows down overall SAT solving time by a
// factor of 3, which we contribute to its slightly less efficient
// implementation.

/*------------------------------------------------------------------------*/

struct LratBuilderClause {
  LratBuilderClause * next;         // collision chain link for hash table
  uint64_t hash;                // previously computed full 64-bit hash
  uint64_t id;                   // id of clause
  bool garbage;                 // for garbage clauses
  unsigned size;
  int literals[0];              // otherwise 'literals' of length 'size'
};

struct LratBuilderWatch {
  int blit;
  unsigned size;
  LratBuilderClause * clause;
  LratBuilderWatch () { }
  LratBuilderWatch (int b, LratBuilderClause * c) :
    blit (b), size (c->size), clause (c)
  { }
};

typedef vector<LratBuilderWatch> LratBuilderWatcher;

/*------------------------------------------------------------------------*/

class LratBuilder : public Observer {

  Internal * internal;

  // Capacity of variable values.
  //
  int64_t size_vars;

  // For the assignment we want to have an as fast access as possible and
  // thus we use an array which can also be indexed by negative literals and
  // is actually valid in the range [-size_vars+1, ..., size_vars-1].
  //
  signed char * vals;
  

  // The 'watchers' and 'marks' data structures are not that time critical
  // and thus we access them by first mapping a literal to 'unsigned'.
  //
  static unsigned l2u (int lit);
  vector<LratBuilderWatcher> watchers;      // watchers of literals
  vector<signed char> marks;            // mark bits of literals

  signed char & mark (int lit);
  signed char & checked_lit (int lit);
  LratBuilderWatcher & watcher (int lit);

  // access by abs(lit)
  static unsigned l2a (int lit);
  vector<LratBuilderClause *> reasons;     // store reason for each assignment
  vector<bool> justified;              // probably better as array ??
  vector<bool> todo_justify;
  vector<signed char> checked_lits;
  LratBuilderClause * conflict;

  bool new_clause_taut;
  bool inconsistent;            // found or added empty clause

  uint64_t num_clauses;         // number of clauses in hash table
  uint64_t num_garbage;         // number of garbage clauses
  uint64_t size_clauses;        // size of clause hash table
  LratBuilderClause ** clauses;     // hash table of clauses
  LratBuilderClause * garbage;      // linked list of garbage clauses

  vector<int> unsimplified;     // original clause for reporting
  vector<int> simplified;       // clause for sorting

  vector<int> trail;            // for propagation

  unsigned next_to_propagate;   // next to propagate on trail

  void enlarge_vars (int64_t idx);
  void import_literal (int lit);
  void import_clause (const vector<int> &);
  bool tautological ();
  LratBuilderClause * assumption;
  LratBuilderClause * inconsistent_clause;
  vector<LratBuilderClause *> unit_clauses;          // we need this because propagate
                                                 // cannot propagate unit clauses
  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces];  // random numbers for hashing
  uint64_t last_hash;           // last computed hash value of clause
  uint64_t last_id;              // id of the last added clause
  uint64_t compute_hash (uint64_t);     // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  void enlarge_clauses ();      // enlarge hash table for clauses
  LratBuilderClause * insert ();               // insert clause in hash table
  LratBuilderClause ** find (const uint64_t);  // find clause position in hash table

  void add_clause (const char * type);

  void collect_garbage_clauses ();

  LratBuilderClause * new_clause ();
  LratBuilderClause * new_unit_clause ();
  LratBuilderClause * new_empty_clause ();
  void delete_clause (LratBuilderClause *);

  signed char val (int lit);            // returns '-1', '0' or '1'

  bool clause_satisfied (LratBuilderClause*);
  bool clause_falsified (LratBuilderClause*);

  void assign (int lit);        // assign a literal to true
  void assign_reason (int lit, LratBuilderClause * reason_clause);
  bool unit_propagate ();
  void unassign_reason (int lit); 
  void assume (int lit);        // assume a literal
  bool propagate ();            // propagate and check for conflicts
  void backtrack (unsigned);    // prepare for next clause
  bool check ();                // check simplified clause is implied
  bool check_lrat ();           // equivalent to check but uses
  vector<uint64_t> build_lrat_proof (int);      // these two functions
  bool check_lrat_proof (vector<uint64_t>);  // instead of simple propagation

  struct {

    int64_t added;              // number of added clauses
    int64_t original;           // number of added original clauses
    int64_t derived;            // number of added derived clauses

    int64_t deleted;            // number of deleted clauses

    int64_t assumptions;        // number of assumed literals
    int64_t propagations;       // number of propagated literals

    int64_t insertions;         // number of clauses added to hash table
    int64_t collisions;         // number of hash collisions in 'find'
    int64_t searches;           // number of searched clauses in 'find'

    int64_t checks;             // number of implication checks

    int64_t collections;        // garbage collections
    int64_t units;

  } stats;

public:

  LratBuilder (Internal *);
  ~LratBuilder ();

  // The following three implement the 'Observer' interface.
  //
  void add_original_clause (uint64_t, const vector<int> &);
  void add_derived_clause (uint64_t, const vector<int> &);
  void delete_clause (uint64_t, const vector<int> &);

  void print_stats ();
  void dump ();                 // for debugging purposes only
};

}

#endif
