#ifndef _tracer_h_INCLUDED
#define _tracer_h_INCLUDED

#include <unordered_map>

namespace CaDiCaL {

class Tracer {

  Internal * internal;
  File * file;
  bool binary;
  bool lrat;
  bool frat;

  int64_t added, deleted;

  uint64_t latest_id;
  vector<uint64_t> delete_ids;

  std::unordered_map<unsigned int, std::vector<int>> id_to_clause;
  std::unordered_map<unsigned int, std::vector<uint64_t>> id_to_premises;
    
  void put_binary_zero ();
  void put_binary_lit (int external_lit);
  void put_binary_id (uint64_t id);
  
  
  // support LRAT
  void lrat_add_clause (uint64_t, const vector<int> &, const vector<uint64_t>&);
  void lrat_delete_clause (uint64_t);

  // support FRAT
  void frat_add_original_clause (uint64_t, const vector<int> &);
  void frat_add_derived_clause (uint64_t, const vector<int> &);
  void frat_add_derived_clause (uint64_t, const vector<int> &, const vector<uint64_t>&);
  void frat_delete_clause (uint64_t, const vector<int> &);
  void frat_finalize_clause (uint64_t, const vector<int> &);

  // support DRAT
  void drat_add_clause (const vector<int> &);
  void drat_delete_clause (const vector<int> &);

public:

  // own and delete 'file'
  Tracer (Internal *);
  Tracer (Internal *, File * file, bool binary, bool lrat, bool frat);
  ~Tracer ();

  uint64_t get_latest_id() const;
  bool is_initial_clause(uint64_t id) const;
  const std::vector<uint64_t>& get_premises(uint64_t id) const;
  const std::vector<int>& get_clause(uint64_t id) const;

  void add_derived_clause (uint64_t, const vector<int> &);
  void add_derived_clause (uint64_t, const vector<int> &, const vector<uint64_t>&);
  void delete_clause (uint64_t, const vector<int> &);
  void add_original_clause (uint64_t, const vector<int> &);       // for frat
  void finalize_clause (uint64_t, const vector<int> &);           // for frat
  void set_first_id (uint64_t);
  
  bool closed ();
  void close ();
  void flush ();
};

}

#endif
