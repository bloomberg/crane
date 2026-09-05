#include "deep_tail_recursion_overflow.h"

DeepTailRecursionOverflow::chain
DeepTailRecursionOverflow::build(uint64_t n,
                                 DeepTailRecursionOverflow::chain acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t k = n - 1;
    return build(k, chain::link(std::move(acc), n));
  }
}

uint64_t
DeepTailRecursionOverflow::total_of(const DeepTailRecursionOverflow::chain &c) {
  if (std::holds_alternative<typename DeepTailRecursionOverflow::chain::End_>(
          c.v())) {
    const auto &[a0] =
        std::get<typename DeepTailRecursionOverflow::chain::End_>(c.v());
    return a0;
  } else {
    const auto &[a0, a1] =
        std::get<typename DeepTailRecursionOverflow::chain::Link>(c.v());
    return (a1 + total_of(*a0));
  }
}
