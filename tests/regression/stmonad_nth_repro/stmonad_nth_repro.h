#ifndef INCLUDED_STMONAD_NTH_REPRO
#define INCLUDED_STMONAD_NTH_REPRO

#include "obj.h"
#include <concepts>
#include <cstdint>
#include <utility>
#include <variant>

struct RefNat;
struct nat_ref;
template <typename I> struct MyEvent;
template <typename CraneInst, typename I>
concept RefClass = requires {
  { CraneInst::refToIx(std::declval<crane::obj>()) } -> std::convertible_to<I>;
};

struct RefNat {
  // DATA
  uint64_t a;

  // ACCESSORS
  RefNat clone() const { return {a}; }

  // CREATORS
  static RefNat mkrefnat(uint64_t a) { return {a}; }

  uint64_t refToIxNat() const {
    const auto &[a] = *this;
    return a;
  }
};

struct nat_ref {
  static uint64_t refToIx(crane::obj _p_a0) {
    RefNat a0 = crane::any_cast<RefNat>(_p_a0);
    return a0.refToIxNat();
  }
};

static_assert(RefClass<nat_ref, uint64_t>);

template <typename I> struct MyEvent {
  // DATA
  uint64_t v_0;

  // ACCESSORS
  MyEvent<I> clone() const { return {v_0}; }

  template <typename CraneU> operator MyEvent<CraneU>() const { return {v_0}; }

  // CREATORS
  static MyEvent<I> newref(uint64_t v_0) { return {v_0}; }
};

uint64_t newOnly();

#endif // INCLUDED_STMONAD_NTH_REPRO
