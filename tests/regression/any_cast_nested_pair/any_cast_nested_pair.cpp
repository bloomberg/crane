#include "any_cast_nested_pair.h"

uint64_t AnyCastNestedPair::apply_pred(AnyCastNestedPair::symbols_semty input) {
  const auto &[v1, rest] =
      crane::any_cast<std::pair<crane::obj, crane::obj>>(input);
  const auto &[v2, _x] =
      crane::any_cast<std::pair<crane::obj, crane::obj>>(rest);
  return (crane::any_cast<uint64_t>(v1) + crane::any_cast<uint64_t>(v2));
}

uint64_t AnyCastNestedPair::test_pred(uint64_t a, uint64_t b) {
  return apply_pred(
      std::make_pair(crane::obj(crane::obj(a)),
                     crane::obj(std::make_pair(crane::obj(crane::obj(b)),
                                               crane::obj(std::monostate{})))));
}
