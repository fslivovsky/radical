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

// TODO: binary FRAT doesn't work anyways!!!
// why bother :/
// fradical works with their tool.
// the problem seem to be the finalize steps. I have them in arbitrary
// order (from the hash-table in lratbuilder) but fradical has them somewhat
// ordered (first empty then units then everything else in ascending order)
// this might actually be what breaks frat-rs (not my fault as far as I can tell)

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
      if (binary) put_binary_id (2*c);                  // because this is lrat
      else file->put (c), file->put (' ');              // we can have negative ids.
  }                                                     // so we need 2*c (cadical
  if (binary) put_binary_zero ();                       // has only rup steps)
  else file->put ("0\n");
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
