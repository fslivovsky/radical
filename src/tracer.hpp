#ifndef _tracer_h_INCLUDED
#define _tracer_h_INCLUDED

// Proof tracing to a file (actually 'File') in DRAT/FRAT format.

namespace CaDiCaL {

class Tracer {

  Internal * internal;
  File * file;
  bool binary;
  bool lrat;

  int64_t added, deleted;

  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);
  
public:

  Tracer (Internal *, File * file, bool binary, bool lrat); // own and delete 'file'
  ~Tracer ();

  void add_derived_clause (uint64_t, const vector<int> &);
  void add_derived_clause (uint64_t, const vector<int> &, const vector<uint64_t>&);
  void delete_clause (uint64_t, const vector<int> &);
  void add_original_clause (uint64_t, const vector<int> &);       // for frat
  void finalize_clause (uint64_t, const vector<int> &);           // for frat

  bool closed ();
  void close ();
  void flush ();
};

}

#endif
