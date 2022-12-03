#include "internal.hpp"

namespace CaDiCaL {

/*------------------------------------------------------------------------*/

Tracer::Tracer (Internal * i, File * f, bool b, bool l) :
  internal (i),
  file (f), binary (b), lrat (l),
  added (0), deleted (0)
{
  (void) internal;
  LOG ("TRACER new");
}

Tracer::~Tracer () {
  LOG ("TRACER delete");
  delete file;
}

/*------------------------------------------------------------------------*/

// Support for binary DRAT format.

inline void Tracer::put_binary_zero () {
  assert (binary);
  assert (file);
  file->put ((unsigned char) 0);
}

inline void Tracer::put_binary_lit (int lit) {
  assert (binary);
  assert (file);
  assert (lit != INT_MIN);
  unsigned x = 2*abs (lit) + (lit < 0);
  unsigned char ch;
  while (x & ~0x7f) {
    ch = (x & 0x7f) | 0x80;
    file->put (ch);
    x >>= 7;
  }
  ch = x;
  file->put (ch);
}

// Support for binary FRAT (TODO: maybe merge with function above
// because this is copy pasta)

inline void Tracer::put_binary_id (uint64_t id) {
  assert (binary);
  assert (file);
  uint64_t x = id;
  unsigned char ch;
  while (x & ~0x7f) {
    ch = (x & 0x7f) | 0x80;
    file->put (ch);
    x >>= 7;
  }
  ch = x;
  file->put (ch);
}

/*------------------------------------------------------------------------*/

void Tracer::add_original_clause (uint64_t id, const vector<int> & clause) { 
  if (file->closed ()) return;
  if (!lrat) return;
  LOG ("TRACER tracing addition of original clause");
  if (binary) file->put ('o');
  else file->put ("o ");
  if (binary) put_binary_id (id);
  else file->put (id), file->put ("  ");
  for (const auto & external_lit : clause)
    if (binary) put_binary_lit (external_lit);
    else file->put (external_lit), file->put (' ');
  if (binary) put_binary_zero ();
  else file->put ("0\n");
}


void Tracer::add_derived_clause (uint64_t id, const vector<int> & clause) {
  if (file->closed ()) return;
  LOG ("TRACER tracing addition of derived clause");
  if (binary) file->put ('a');
  else if (lrat) file->put ("a ");
  if (lrat) {
    if (binary) put_binary_id (id);
    else file->put (id), file->put ("  ");
  }
  for (const auto & external_lit : clause)
    if (binary) put_binary_lit (external_lit);
    else file->put (external_lit), file->put (' ');
  if (binary) put_binary_zero ();
  else file->put ("0\n");
  added++;
}


void Tracer::add_derived_clause (uint64_t id, const vector<int> & clause, const vector<uint64_t> & chain) {
  if (file->closed ()) return;
  LOG ("TRACER tracing addition of derived clause with proof chain");
  if (binary) file->put ('a');
  else if (lrat) file->put ("a ");
  if (lrat) {
    if (binary) put_binary_id (id);
    else file->put (id), file->put ("  ");
  }
  for (const auto & external_lit : clause)
    if (binary) put_binary_lit (external_lit);
    else file->put (external_lit), file->put (' ');
  if (lrat) {
    if (binary) put_binary_zero (), file->put ('l');
    else file->put ("0  l ");
    for (const auto & c : chain)
      if (binary) put_binary_id (2*c);        // lrat can have negative ids
      else file->put (c), file->put (' ');    // in proof chain, so they get
  }                                           // represented by 2*|id|+(id<0)
  if (binary) put_binary_zero ();             // since cadical has no rat-steps
  else file->put ("0\n");                     // this is just 2c here 
  added++;
}

void Tracer::delete_clause (uint64_t id, const vector<int> & clause) {
  if (file->closed ()) return;
  LOG ("TRACER tracing deletion of clause");
  if (binary) file->put ('d');
  else file->put ("d ");
  if (lrat) {
    if (binary) put_binary_id (id);
    else file->put (id), file->put ("  ");
  }
  for (const auto & external_lit : clause)
    if (binary) put_binary_lit (external_lit);
    else file->put (external_lit), file->put (' ');
  if (binary) put_binary_zero ();
  else file->put ("0\n");
  deleted++;
}

void Tracer::finalize_clause (uint64_t id, const vector<int> & clause) {
  if (!lrat) return;
  if (file->closed ()) return;
  LOG ("TRACER tracing finalization of clause");
  if (binary) file->put ('f');
  else file->put ("f ");
  if (binary) put_binary_id (id);
  else file->put (id), file->put ("  ");
  for (const auto & external_lit : clause)
    if (binary) put_binary_lit (external_lit);
    else file->put (external_lit), file->put (' ');
  if (binary) put_binary_zero ();
  else file->put ("0\n");
}


/*------------------------------------------------------------------------*/

bool Tracer::closed () { return file->closed (); }

void Tracer::close () { assert (!closed ()); file->close (); }

void Tracer::flush () {
  assert (!closed ());
  file->flush ();
  MSG ("traced %" PRId64 " added and %" PRId64 " deleted clauses",
    added, deleted);
}

}
