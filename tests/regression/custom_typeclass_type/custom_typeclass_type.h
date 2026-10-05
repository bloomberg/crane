#ifndef INCLUDED_CUSTOM_TYPECLASS_TYPE
#define INCLUDED_CUSTOM_TYPECLASS_TYPE

#include "obj.h"
#include <concepts>
#include <cstdint>
#include <utility>

struct RefNat;
struct nat_ref;
template <typename CraneInst, typename I>
concept RefClass = requires {
  {
    CraneInst::template mkRef<crane::obj>(std::declval<I>())
  } -> std::convertible_to<crane::obj>;
};

struct RefNat {
  // DATA
  uint64_t a;

  // ACCESSORS
  RefNat clone() const { return {a}; }

  // CREATORS
  static RefNat mkref(uint64_t a) { return {a}; }
};

struct nat_ref {
  template <typename CraneA0> static CraneA0 mkRef(uint64_t i) {
    return CraneA0::mkref(i);
  }
};

static_assert(RefClass<nat_ref, uint64_t>);
uint64_t test_new();

#endif // INCLUDED_CUSTOM_TYPECLASS_TYPE
