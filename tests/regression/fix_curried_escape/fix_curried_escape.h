#ifndef INCLUDED_FIX_CURRIED_ESCAPE
#define INCLUDED_FIX_CURRIED_ESCAPE

#include "fn.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <utility>

struct FixCurriedEscape {
  /// A local fixpoint that escapes through an option wrapper,
  /// preventing Crane from uncurrying it away.
  ///
  /// make_fn defines a local fixpoint go with & capture of
  /// base (a stack variable).  Wrapping in Some forces
  /// the fixpoint to be stored as a std::function, because the
  /// return type option (nat -> nat) cannot be uncurried.
  ///
  /// BUG: The std::function holds & references to base.
  /// After make_fn returns, base is destroyed, and calling
  /// the extracted function accesses freed memory.
  static std::optional<crane::fn<uint64_t(uint64_t)>> make_fn(uint64_t base);
  /// test1: unwrap and call — go captures base=42.
  /// go 3 = 42 + 3 = 45.
  static constexpr uint64_t test1 = UINT64_C(45);
  /// test2: Different base to clobber the stack.
  /// make_fn 10 -> go captures base=10.
  /// go 7 = 10 + 7 = 17.
  static constexpr uint64_t test2 = UINT64_C(17);
  /// test3: Call make_fn twice — stack reuse should clobber base.
  /// First call returns go1 with base=100.
  /// Second call reuses the stack frame with base=0.
  /// If go1 reads the clobbered base, it returns 0+5=5 instead of 100+5=105.
  static constexpr uint64_t test3 = UINT64_C(105);
};

#endif // INCLUDED_FIX_CURRIED_ESCAPE
