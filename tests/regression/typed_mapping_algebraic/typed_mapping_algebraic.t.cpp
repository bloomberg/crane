// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// A typed-mapped enumeration (std::uint8_t) and option-like type
// (std::optional), built and matched from Rocq.
#include <typed_mapping_algebraic.h>

#include <cstdint>
#include <iostream>
#include <optional>
#include <type_traits>

using T = TypedMappingAlgebraic;

static int failures = 0;

static void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAIL: " << what << "\n";
    ++failures;
  }
}

int main() {
  // The structured canonical types reach the signatures.
  static_assert(std::is_same_v<decltype(T::next_suit(std::uint8_t{0})), std::uint8_t>);
  static_assert(std::is_same_v<decltype(T::suit_of_code(1)), std::optional<std::uint8_t>>);

  check(T::suit_code(0) == 1, "suit_code Hearts");
  check(T::suit_code(1) == 2, "suit_code Spades");
  check(T::suit_code(2) == 3, "suit_code Clubs");
  check(T::next_suit(0) == 1 && T::next_suit(1) == 2 && T::next_suit(2) == 0, "next_suit");

  check(T::suit_of_code(1) == std::optional<std::uint8_t>{0}, "suit_of_code 1");
  check(T::suit_of_code(3) == std::optional<std::uint8_t>{2}, "suit_of_code 3");
  check(!T::suit_of_code(0).has_value(), "suit_of_code 0");
  check(!T::suit_of_code(7).has_value(), "suit_of_code 7");

  check(T::maybe_default<uint64_t>(std::optional<uint64_t>{5}, 9) == 5, "maybe_default Just");
  check(T::maybe_default<uint64_t>(std::nullopt, 9) == 9, "maybe_default Nothing");

  // Hearts -> Spades -> 2; Clubs -> Hearts -> 1; no suit -> 0.
  check(T::code_after(1) == 2, "code_after 1");
  check(T::code_after(3) == 1, "code_after 3");
  check(T::code_after(4) == 0, "code_after 4");

  auto l = List<std::optional<uint64_t>>::cons(
      std::optional<uint64_t>{3},
      List<std::optional<uint64_t>>::cons(
          std::nullopt, List<std::optional<uint64_t>>::cons(
                            std::optional<uint64_t>{4},
                            List<std::optional<uint64_t>>::nil())));
  check(T::lengths(l) == 7, "lengths");

  if (failures == 0) {
    std::cout << "All typed_mapping_algebraic tests passed!\n";
    return 0;
  }
  return 1;
}
