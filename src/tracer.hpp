#ifndef _tracer_h_INCLUDED
#define _tracer_h_INCLUDED

#include "observer.hpp" // Alphabetically after 'tracer'.

// Proof tracing to a file (actually 'File') in DRAT format.

namespace CaDiCaL {

class Tracer : public Observer {

  Internal * internal;
  File * file;
  bool binary;
  bool lrat;

  int64_t added, deleted;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);

public:

  Tracer (Internal *, File * file, bool binary, bool lrat); // own and delete 'file'
  ~Tracer ();

  void add_derived_clause (uint64_t, const vector<int> &);
  void add_derived_clause (uint64_t, const vector<int> &, const vector<uint64_t>&);
  void delete_clause (uint64_t, const vector<int> &);
  void add_original_clause (uint64_t, const vector<int> &) { assert(false); }
  vector<uint64_t> add_clause_get_proof (uint64_t, const vector<int> &) {
    vector<uint64_t> a; assert (false); return a;  // should not be called
  }

  bool closed ();
  void close ();
  void flush ();
};

}

#endif
