#include "outer_member_shadowed_by_nested.h"

uint64_t OuterMemberShadowedByNested::f(uint64_t n) {
  return (n + UINT64_C(1));
}

uint64_t OuterMemberShadowedByNested::Sub::f(uint64_t n) {
  return (UINT64_C(2) * f(n));
}

OuterMemberShadowedByNested::reader
OuterMemberShadowedByNested::read_with(OuterMemberShadowedByNested::tree t) {
  return reader::reader0(
      [=, t = std::move(t)](uint64_t x) { return (x + t.sum()); });
}
