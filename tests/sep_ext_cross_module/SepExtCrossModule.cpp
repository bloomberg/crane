#include "SepExtCrossModule.h"

#include "Datatypes.h"
#include "List.h"

namespace SepExtCrossModule {

uint64_t sum_list(const Datatypes::List<uint64_t> &l) {
  return l.template fold_left<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); },
      UINT64_C(0));
}

Datatypes::List<uint64_t> make_pair_list(uint64_t n, uint64_t m) {
  return Datatypes::template List<uint64_t>::cons(
      n, Datatypes::template List<uint64_t>::cons(
             m, Datatypes::template List<uint64_t>::nil()));
}

} // namespace SepExtCrossModule
