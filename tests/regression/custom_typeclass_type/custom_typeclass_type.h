#ifndef INCLUDED_CUSTOM_TYPECLASS_TYPE
#define INCLUDED_CUSTOM_TYPECLASS_TYPE

#include <any>
#include <concepts>
#include <utility>

struct RefNat {
  // DATA
  uint64_t a;

  // ACCESSORS
  RefNat clone() const { return {a}; }

  // CREATORS
  static RefNat mkref(uint64_t a) { return {a}; }
};

template <typename _Inst, typename I>
concept RefClass = requires {
  { _Inst::mkRef(std::declval<I>()) } -> std::convertible_to<std::any>;
};

struct nat_ref {
  static std::any mkRef(uint64_t i) { return RefNat::mkref(i); }
};

static_assert(RefClass<nat_ref, uint64_t>);
uint64_t test_new();

#endif // INCLUDED_CUSTOM_TYPECLASS_TYPE
