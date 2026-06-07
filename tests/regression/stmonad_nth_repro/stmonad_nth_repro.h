#ifndef INCLUDED_STMONAD_NTH_REPRO
#define INCLUDED_STMONAD_NTH_REPRO

#include <any>
#include <concepts>
#include <variant>

struct RefNat {
  // DATA
  uint64_t a;

  // ACCESSORS
  RefNat clone() const { return {a}; }

  // CREATORS
  static RefNat mkrefnat(uint64_t a) { return {a}; }

  template <typename T1> uint64_t refToIxNat() const {
    const auto &[a] = *this;
    return a;
  }
};

template <typename I, typename I>
concept RefClass = requires(std::any a0, std::any a1) {
  { I::refToIx(a0, a1) } -> std::convertible_to<I>;
};

struct nat_ref {
  static uint64_t refToIx(std::any) {
    return [](const auto &_x) { return _x.refToIxNat(); };
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
