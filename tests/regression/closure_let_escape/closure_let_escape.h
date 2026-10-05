#ifndef INCLUDED_CLOSURE_LET_ESCAPE
#define INCLUDED_CLOSURE_LET_ESCAPE

#include "fn.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

struct ClosureLetEscape {
  /// A local fixpoint captures a LET-BINDING (not a function parameter)
  /// and escapes through Some (std::optional).
  ///
  /// BUG: Local fixpoints use & capture. The let-binding base is a
  /// stack variable. The fixpoint escapes through Some, so
  /// return_captures_by_value does NOT apply. After the function
  /// returns, base is destroyed, and the captured reference dangles.
  ///
  /// Difference from fix_escape_capture: captures a LET-BINDING
  /// (not a function parameter). The let-binding involves a computation
  /// (n * 2), so it can't be optimized away.
  static std::optional<crane::fn<uint64_t(uint64_t)>> make_fn_fix(uint64_t n);
  /// test1: make_fn_fix(21) => base=42, Some(add).
  /// add(3) = 42 + 3 = 45.
  /// Bug: & captures dangling reference to base.
  static constexpr uint64_t test1 = UINT64_C(45);
  /// test2: With noise between closure creation and invocation.
  /// base = 100, noise = 15, add(noise) = 100 + 15 = 115.
  static constexpr uint64_t test2 = UINT64_C(115);
  /// test3: Captures from multiple let bindings.
  /// BUG: Both a and b are captured by &, both dangle.
  static std::optional<crane::fn<uint64_t(uint64_t)>> make_fn_multi(uint64_t n);
  static constexpr uint64_t test3 = UINT64_C(49);
};

#endif // INCLUDED_CLOSURE_LET_ESCAPE
