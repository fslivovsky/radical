#ifndef _observer_hpp_INCLUDED
#define _observer_hpp_INCLUDED

namespace CaDiCaL {

// Proof observer class used to act on added, derived or deleted clauses.

class Observer {

public:

  Observer () { }
  virtual ~Observer () { }

  // An online proof 'Checker' needs to know original clauses too while a
  // proof 'Tracer' will not implement this function.
  //
  virtual void add_original_clause (uint64_t, const vector<int> &) { }

  // Notify the observer that a new clause has been derived.
  //
  virtual void add_derived_clause (uint64_t, const vector<int> &) { }

  // Notify the observer that a new clause has been derived.
  //
  virtual vector<uint64_t> add_clause_get_proof (uint64_t, const vector<int> &) {
    vector<uint64_t> a;
    return a;
  }

  // Notify the observer that a new clause has been derived and give lrat proof chain.
  //
  virtual void add_derived_clause (uint64_t, const vector<int> &, const vector<uint64_t> &) { }

  // Notify the observer that a clause is not used anymore.
  //
  virtual void delete_clause (uint64_t, const vector<int> &) { }

  virtual void flush () { }
};

}

#endif
