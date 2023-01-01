#ifndef _decompose_hpp_INCLUDED
#define _decompose_hpp_INCLUDED

namespace CaDiCaL {

#define TRAVERSED UINT_MAX              // mark completely traversed

struct DFS {
  unsigned idx;                         // depth first search index
  unsigned min;                         // minimum reachable index
  uint64_t id;                          // for lrat
  int parent;                           // for lrat
  DFS () : idx (0), min (0), id (0), parent (0) { }
};

}

#endif
