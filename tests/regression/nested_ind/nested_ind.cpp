#include "nested_ind.h"

NestedInd::rose<uint64_t> NestedInd::leaf(uint64_t n) {
  return rose<uint64_t>::node(n,
                              custom_list<NestedInd::rose<uint64_t>>::cnil());
}
