#include "option_nested_recursion_bad_cpp.h"

OptionNestedRecursionBadCpp::chain
OptionNestedRecursionBadCpp::build(uint64_t n) {
  if (n <= 0) {
    return chain::link(UINT64_C(0),
                       std::optional<OptionNestedRecursionBadCpp::chain>());
  } else {
    uint64_t m = n - 1;
    return chain::link(
        n, std::make_optional<OptionNestedRecursionBadCpp::chain>(build(m)));
  }
}

uint64_t OptionNestedRecursionBadCpp::depth(
    const OptionNestedRecursionBadCpp::chain &c) {
  const auto &[a0, a1] =
      std::get<typename OptionNestedRecursionBadCpp::chain::Link>(c.v());
  if ((*a1).has_value()) {
    const OptionNestedRecursionBadCpp::chain &c_ = *(*a1);
    return (depth(c_) + 1);
  } else {
    return UINT64_C(1);
  }
}

uint64_t OptionNestedRecursionBadCpp::run(uint64_t n) {
  return depth(build(n));
}
