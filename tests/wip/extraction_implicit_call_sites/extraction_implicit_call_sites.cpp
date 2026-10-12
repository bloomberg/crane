#include "extraction_implicit_call_sites.h"

uint64_t ExtractionImplicitCallSites::count(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    return ([=](List<uint64_t> _x0) -> uint64_t {
      return count(a1_value, _x0);
    } + 1);
  }
}
