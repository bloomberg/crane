#ifndef INCLUDED_EXISTENTIAL_FN_PROJECTION
#define INCLUDED_EXISTENTIAL_FN_PROJECTION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <functional>
#include <stdexcept>
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

  P projT2() const {
    const auto &[x0, a1] = *this;
    return a1;
  }
};

struct ExistentialFnProjection {
  static inline const SigT<crane::obj, crane::obj> measurer =
      SigT<crane::obj, crane::obj>::existt(
          crane::obj(),
          crane_erase_fn([](const crane::obj &_any_x) -> uint64_t {
            uint64_t x = crane::any_cast<uint64_t>(_any_x);
            return (crane::any_cast<uint64_t>(x) + UINT64_C(1));
          }));
  static inline const uint64_t measured = crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(measurer.projT2())(
          crane::obj(UINT64_C(4))));
  static inline const SigT<crane::obj, std::pair<crane::obj, crane::obj>>
      tagged = SigT<crane::obj, std::pair<crane::obj, crane::obj>>::existt(
          crane::obj(),
          std::make_pair(crane::obj(UINT64_C(7)), crane::obj(UINT64_C(8))));
  static inline const uint64_t tag = crane::any_cast<uint64_t>(
      crane_any_cast<std::pair<crane::obj, crane::obj>>(tagged.projT2())
          .second);
};

#endif // INCLUDED_EXISTENTIAL_FN_PROJECTION
