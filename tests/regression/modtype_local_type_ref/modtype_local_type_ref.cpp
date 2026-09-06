#include "modtype_local_type_ref.h"

uint64_t ModtypeLocalTypeRef::S::lookup(const std::pair<uint64_t, uint64_t> &e,
                                        uint64_t k) {
  if (e.first == k) {
    return e.second;
  } else {
    return UINT64_C(0);
  }
}

ModtypeLocalTypeRef::point
ModtypeLocalTypeRef::T::shift(const ModtypeLocalTypeRef::point &p, uint64_t d) {
  return point{(p.px + d), p.py};
}
