#include "global_indexed_value_type.h"

/// At a concrete element type.
List<List<uint64_t>> GlobalIndexedValueType::lists_concrete(uint64_t n) {
  std::shared_ptr<crane::array_storage<List<uint64_t>>> arr =
      std::make_shared<crane::array_storage<List<uint64_t>>>(
          static_cast<std::size_t>(n), List<uint64_t>::nil());
  std::span{*arr}[UINT64_C(0)] =
      List<uint64_t>::cons(UINT64_C(7), List<uint64_t>::nil());
  return crane::st::elems<List<List<uint64_t>>>(std::span{std::as_const(*arr)});
}

List<List<uint64_t>> GlobalIndexedValueType::via_notation(uint64_t n) {
  return lists_notation<uint64_t>(n, UINT64_C(1), UINT64_C(2));
}

List<List<uint64_t>> GlobalIndexedValueType::via_definition(uint64_t n) {
  return lists_definition<uint64_t>(n, UINT64_C(3), UINT64_C(4));
}

uint64_t GlobalIndexedValueType::number() {
  return number_definition<uint64_t>(UINT64_C(9));
}
