#ifndef INCLUDED_SIGT_BRANCH_TYPE_MISMATCH
#define INCLUDED_SIGT_BRANCH_TYPE_MISMATCH

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <utility>

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

/// A sigT over a boolean-indexed type family whose branches are nat and
/// nat -> nat: the payload is erased to std::any, so the function branch
/// must be called through the canonical erased-callable adapter and its
/// result unboxed.
struct SigtBranchTypeMismatch {
  static inline const SigT<bool, crane::obj> pack =
      SigT<bool, crane::obj>::existt(
          false, crane_erase_fn([](const crane::obj &_any_n) {
            uint64_t n = crane::any_cast<uint64_t>(_any_n);
            return (n + UINT64_C(7));
          }));
  static constexpr uint64_t go = UINT64_C(8);
};

#endif // INCLUDED_SIGT_BRANCH_TYPE_MISMATCH
