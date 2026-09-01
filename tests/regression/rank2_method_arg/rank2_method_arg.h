#ifndef INCLUDED_RANK2_METHOD_ARG
#define INCLUDED_RANK2_METHOD_ARG

#include "crane_fn.h"
#include <any>
#include <concepts>
#include <functional>
#include <utility>

/// A class method taking a rank-2 polymorphic function.  The instance
/// applies it at nat, but the erased callback returns std::any where the
/// method's declared uint64_t return type is required.
template <typename I>
concept Applyer = requires {
  {
    I::app2(std::declval<std::function<std::any(std::any)>>(),
            std::declval<uint64_t>())
  } -> std::convertible_to<uint64_t>;
};

struct Rank2MethodArg {
  struct AI {
    static uint64_t app2(std::function<std::any(std::any)> f, uint64_t n) {
      return std::any_cast<uint64_t>(f(n));
    }
  };

  static_assert(Applyer<AI>);
  static uint64_t run(uint64_t k);
};

#endif // INCLUDED_RANK2_METHOD_ARG
