#ifndef INCLUDED_STMONAD_NTH_REPRO
#define INCLUDED_STMONAD_NTH_REPRO

#include <any>
#include <concepts>
#include <utility>
#include <variant>

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

template <typename _Inst, typename I>
concept RefClass = requires {
  { _Inst::refToIx(std::declval<std::any>()) } -> std::convertible_to<I>;
};

struct nat_ref {
  static uint64_t refToIx(std::any _p_a0) {
    RefNat a0 = std::any_cast<RefNat>(_p_a0);
    return a0.refToIxNat();
  }
};

static_assert(RefClass<nat_ref, uint64_t>);

template <typename I> struct MyEvent {
  // DATA
  uint64_t v;

  // ACCESSORS
  MyEvent<I> clone() const { return {v}; }

  // CREATORS
  static MyEvent<I> newref(uint64_t v) { return {v}; }
};

uint64_t newOnly();

#endif // INCLUDED_STMONAD_NTH_REPRO
