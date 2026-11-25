#pragma once

#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

/// A recursive call made through a coercion of its callee is a recursive
/// call.
///
/// Nat.even_EvenT calls itself as (magic even_EvenT) n', the coercion
/// standing for the change of index in its result type, and the C++ calls
/// even_EvenT(n1) where it stands, below the frame that binds the result.
/// The recursion plan read only a callee written as a bare global, saw no
/// recursion, and the function was left calling itself: half of two
/// million ran two million C++ frames deep.
struct LoopifyCoercedSelfCall {
  static uint64_t half(uint64_t n);
};

struct Nat {
  using EvenT = uint64_t;
  [[gnu::used]] static inline const EvenT EvenT_0 = UINT64_C(0);
  static EvenT EvenT_2(uint64_t _x, uint64_t h0);
  static EvenT even_EvenT(uint64_t n);
};
