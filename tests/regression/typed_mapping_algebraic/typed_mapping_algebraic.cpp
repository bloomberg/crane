#include "typed_mapping_algebraic.h"

uint64_t TypedMappingAlgebraic::suit_code(std::uint8_t s) {
  if (s == 0) {
    return UINT64_C(1);
  } else if (s == 1) {
    return UINT64_C(2);
  } else {
    return UINT64_C(3);
  }
}

std::uint8_t TypedMappingAlgebraic::next_suit(std::uint8_t s) {
  if (s == 0) {
    return std::uint8_t{1};
  } else if (s == 1) {
    return std::uint8_t{2};
  } else {
    return std::uint8_t{0};
  }
}

std::optional<std::uint8_t> TypedMappingAlgebraic::suit_of_code(uint64_t n) {
  if (n <= 0) {
    return std::optional<std::uint8_t>{};
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return std::optional<std::uint8_t>{std::uint8_t{0}};
    } else {
      uint64_t n1 = n0 - 1;
      if (n1 <= 0) {
        return std::optional<std::uint8_t>{std::uint8_t{1}};
      } else {
        uint64_t n2 = n1 - 1;
        if (n2 <= 0) {
          return std::optional<std::uint8_t>{std::uint8_t{2}};
        } else {
          uint64_t _x = n2 - 1;
          return std::optional<std::uint8_t>{};
        }
      }
    }
  }
}

uint64_t TypedMappingAlgebraic::code_after(uint64_t n) {
  return maybe_default<uint64_t>(
      maybe_map<std::uint8_t, uint64_t>(
          [](std::uint8_t s) { return suit_code(next_suit(s)); },
          suit_of_code(n)),
      UINT64_C(0));
}

uint64_t
TypedMappingAlgebraic::lengths(const List<std::optional<uint64_t>> &l) {
  return l.template fold_left<uint64_t>(
      [](uint64_t acc,
         std::optional<uint64_t> m) {
        return acc + maybe_default<uint64_t>(m, UINT64_C(0));
      },
      UINT64_C(0));
}
