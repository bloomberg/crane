#ifndef INCLUDED_OPAQUE
#define INCLUDED_OPAQUE

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <utility>

template <typename A> struct Sig;

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct Opaque {
  static uint64_t safe_pred(uint64_t n);
  static uint64_t pred_of_succ(uint64_t n);
  static bool nat_eq_dec(uint64_t n, uint64_t x);
  static bool are_equal(uint64_t n, uint64_t m);
  static Sig<uint64_t> bounded_add(uint64_t x0_, uint64_t x1_, uint64_t x2_);
  static constexpr uint64_t test_safe_pred = UINT64_C(4);
  static constexpr uint64_t test_pred_succ = UINT64_C(7);
  static constexpr bool test_eq_true = true;
  static constexpr bool test_eq_false = false;
};

#endif // INCLUDED_OPAQUE
