#ifndef INCLUDED_SIGT_BRANCH_TYPE_MISMATCH
#define INCLUDED_SIGT_BRANCH_TYPE_MISMATCH

#include <any>
#include <functional>
#include <utility>
#include <variant>

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

/// WIP: A `sigT` over a boolean-indexed type family whose branches are `nat`
/// and `nat -> nat` extracts to a single lambda whose two branches return
/// `uint64_t` and `std::any`, which clang rejects.
struct SigtBranchTypeMismatch {
  static inline const SigT<bool, std::any> pack = SigT<bool, std::any>::existt(
      false, std::function<std::any(std::any)>([](const std::any &_any_n) {
        uint64_t n = std::any_cast<uint64_t>(_any_n);
        return (n + UINT64_C(7));
      }));
  static inline const uint64_t go = []() {
    const auto &_sv0 = pack;
    const auto &[x0, a10] = _sv0;
    if (x0) {
      return std::any_cast<uint64_t>(a10);
    } else {
      return std::any_cast<std::function<std::any(std::any)>>(a10)(UINT64_C(1));
    }
  }();
};

#endif // INCLUDED_SIGT_BRANCH_TYPE_MISMATCH
