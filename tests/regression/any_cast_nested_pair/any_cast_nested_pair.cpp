#include "any_cast_nested_pair.h"

uint64_t AnyCastNestedPair::apply_pred(AnyCastNestedPair::symbols_semty input) {
  const auto &[v1, rest] = std::any_cast<std::pair<std::any, std::any>>(input);
  const auto &[v2, _x] = std::any_cast<std::pair<std::any, std::any>>(rest);
  return (std::any_cast<uint64_t>(v1) + std::any_cast<uint64_t>(v2));
}

uint64_t AnyCastNestedPair::test_pred(uint64_t a, uint64_t b) {
  return apply_pred(std::make_pair(
      std::any(a), std::make_pair(std::any(b), std::monostate{})));
}
