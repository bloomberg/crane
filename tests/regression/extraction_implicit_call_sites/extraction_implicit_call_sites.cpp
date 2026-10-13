#include "extraction_implicit_call_sites.h"

uint64_t ExtractionImplicitCallSites::count(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return (count(*a1) + 1);
  }
}
