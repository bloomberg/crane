#include "triple_list_drain.h"

TripleListDrain::t TripleListDrain::wrap(uint64_t k, TripleListDrain::t acc) {
  return t::node(k,
                 List<List<List<TripleListDrain::t>>>::cons(
                     List<List<TripleListDrain::t>>::cons(
                         List<TripleListDrain::t>::cons(
                             std::move(acc), List<TripleListDrain::t>::nil()),
                         List<List<TripleListDrain::t>>::nil()),
                     List<List<List<TripleListDrain::t>>>::nil()));
}
