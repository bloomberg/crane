#ifndef INCLUDED_ERASED_UNIT_RESULT
#define INCLUDED_ERASED_UNIT_RESULT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <functional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (crane_convertible<_U0, const A &>) {
                return crane_convert<_U0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const P &>) {
                return crane_convert<_U1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
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
    requires std::is_invocable_r_v<void, F0 &, T1 &>
  static void run_twice(F0 &&f, const T1 &x) {
    {
      f(x);
      return;
    }
  }

  static bool is_tt(std::monostate u);
  static bool
  through_sig(const SigT<crane::obj, std::pair<crane::obj, crane::obj>> &p);
  static inline const bool check =
      through_sig(SigT<crane::obj, std::pair<crane::obj, crane::obj>>::existt(
          crane::obj(), std::make_pair(crane::obj(crane_erase_fn(touch)),
                                       crane::obj(UINT64_C(3)))));
};

#endif // INCLUDED_ERASED_UNIT_RESULT
