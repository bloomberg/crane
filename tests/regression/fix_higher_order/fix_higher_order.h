#ifndef INCLUDED_FIX_HIGHER_ORDER
#define INCLUDED_FIX_HIGHER_ORDER

#include "fn.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

struct FixHigherOrder {
  /// A wrapper function that takes a function and stores it in Some.
  template <typename F0>
  static std::optional<crane::fn<uint64_t(uint64_t)>> wrap_fn(F0 &&f) {
    return std::make_optional<crane::fn<uint64_t(uint64_t)>>(f);
  }

  /// Creates a fixpoint and passes it through wrap_fn.
  /// The fixpoint escapes through the function call, not through
  /// direct constructor application.
  ///
  /// BUG HYPOTHESIS: When the fixpoint is passed as an argument to
  /// wrap_fn, the translation may use & capture. wrap_fn stores
  /// it in Some and returns. After make_wrapped returns, the
  /// captured base is destroyed.
  static std::optional<crane::fn<uint64_t(uint64_t)>>
  make_wrapped(uint64_t base);
  /// test1: make_wrapped(5) -> Some(go), go(3) = 5+3 = 8.
  static constexpr uint64_t test1 = UINT64_C(8);
  /// test2: with noise between creation and use.
  static constexpr uint64_t test2 = UINT64_C(67);

  /// Two layers of wrapping: fixpoint passed through two functions.
  template <typename F0>
  static std::optional<std::optional<crane::fn<uint64_t(uint64_t)>>>
  double_wrap(F0 &&f) {
    return std::make_optional<std::optional<crane::fn<uint64_t(uint64_t)>>>(
        std::make_optional<crane::fn<uint64_t(uint64_t)>>(f));
  }

  static std::optional<std::optional<crane::fn<uint64_t(uint64_t)>>>
  make_double_wrapped(uint64_t base);
  /// test3: Doubly wrapped fixpoint. go(7) = 100+7 = 107.
  static constexpr uint64_t test3 = UINT64_C(107);
};

#endif // INCLUDED_FIX_HIGHER_ORDER
