#ifndef INCLUDED_ERASED_UNIT_RESULT
#define INCLUDED_ERASED_UNIT_RESULT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <functional>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const P &>
  operator SigT<CraneU0, CraneU1>() const {
    return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1)};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct ErasedUnitResult {
  static void touch(uint64_t _x);
  static inline const SigT<crane::obj, crane::obj> packed =
      SigT<crane::obj, crane::obj>::existt(crane::obj(), crane_erase_fn(touch));
  static inline const SigT<crane::obj, crane::obj> boxed =
      SigT<crane::obj, crane::obj>::existt(crane::obj(), crane_erase_fn(touch));

  template <typename T1, typename F0>
  static void run_twice(F0 &&f, const T1 &x) {
    {
      f(x);
      return;
    }
  }

  static bool is_tt(std::monostate u);
  static bool
  through_sig(const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &p);

  static constexpr bool check = true;
};

#endif // INCLUDED_ERASED_UNIT_RESULT
