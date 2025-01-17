#ifndef _lratchecker_hpp_INCLUDED
#define _lratchecker_hpp_INCLUDED

/*------------------------------------------------------------------------*/

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

// This checker implements an LRUP checker.
// It requires LRAT-style proof chains for each learned clause that we can
// currently only build with lratbuilder.
//
// Most of the infrastructure is taken from checker, but without the propagation

/*------------------------------------------------------------------------*/

struct LratCheckerClause {
  LratCheckerClause * next;         // collision chain link for hash table
  uint64_t hash;                // previously computed full 64-bit hash
  uint64_t id;                   // id of clause
  bool garbage;                 // for garbage clauses
  unsigned size;
  bool used;
  bool tautological;
  int literals[0];              // 'literals' of length 'size'
};

/*------------------------------------------------------------------------*/

class LratChecker {

  Internal * internal;

  // Capacity of variable values.
  //
  int64_t size_vars;

  // The 'watchers' and 'marks' data structures are not that time critical
  // and thus we access them by first mapping a literal to 'unsigned'.
  //
  static unsigned l2u (int lit);


  signed char & checked_lit (int lit);
  signed char & mark (int lit);

  vector<signed char> checked_lits;
  vector<signed char> marks;            // mark bits of literals

  uint64_t num_clauses;         // number of clauses in hash table
  uint64_t num_garbage;         // number of garbage clauses
  uint64_t size_clauses;        // size of clause hash table
  LratCheckerClause ** clauses;     // hash table of clauses
  LratCheckerClause * garbage;      // linked list of garbage clauses

  vector<int> imported_clause;     // original clause for reporting

  void enlarge_vars (int64_t idx);
  void import_literal (int lit);
  void import_clause (const vector<int> &);

  static const unsigned num_nonces = 4;

  uint64_t nonces[num_nonces];  // random numbers for hashing
  uint64_t last_hash;           // last computed hash value of clause
  uint64_t last_id;              // id of the last added clause
  uint64_t compute_hash (uint64_t);     // compute and save hash value of clause

  // Reduce hash value to the actual size.
  //
  static uint64_t reduce_hash (uint64_t hash, uint64_t size);

  void enlarge_clauses ();      // enlarge hash table for clauses
  void insert ();               // insert clause in hash table
  LratCheckerClause ** find (const uint64_t);  // find clause position in hash table

  void add_clause (const char * type);

  void collect_garbage_clauses ();

  LratCheckerClause * new_clause ();
  void delete_clause (LratCheckerClause *);

  bool check (vector<uint64_t>);    // check if new clause is implied by rup
  bool check_resolution (vector<uint64_t>); // check if new clause is implied by resolution

  struct {

    int64_t added;              // number of added clauses
    int64_t original;           // number of added original clauses
    int64_t derived;            // number of added derived clauses

    int64_t deleted;            // number of deleted clauses

    int64_t insertions;         // number of clauses added to hash table
    int64_t collisions;         // number of hash collisions in 'find'
    int64_t searches;           // number of searched clauses in 'find'

    int64_t checks;             // number of implication checks

    int64_t collections;        // garbage collections

  } stats;

public:

  LratChecker (Internal *);
  ~LratChecker ();

  void add_original_clause (uint64_t, const vector<int> &);
  // check the proof chain for the new clause and add it to the checker
  void add_derived_clause (uint64_t, const vector<int> &, const vector<uint64_t> &);

  // used for frat. just assume the clause is correct because we have no proof.
  void add_derived_clause (uint64_t, const vector<int> &);

  // check if the clause is present and delete it from the checker
  void delete_clause (uint64_t, const vector<int> &);

  void print_stats ();
  void dump ();                 // for debugging purposes only
};

}

#endif
