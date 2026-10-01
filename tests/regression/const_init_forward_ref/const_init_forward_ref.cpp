#include "const_init_forward_ref.h"

tbl Store::build(const List<uint64_t> &t) {
  return List<uint64_t>::cons(UINT64_C(1), t);
}
