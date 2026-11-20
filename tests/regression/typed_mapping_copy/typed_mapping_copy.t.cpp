// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Parameters of typed-mapped types are passed as their copy and access
// models say, next to a legacy-mapped std::optional.
#include <typed_mapping_copy.h>

#include <array>
#include <cstdint>
#include <iostream>
#include <optional>
#include <type_traits>
#include <vector>

using T = TypedMappingCopy;
using Bag = std::vector<uint64_t>;

// BitCopy + ReadByValue: by value.
static_assert(std::is_same_v<decltype(&T::flag_both), bool (*)(bool, bool)>);
// DuplicateValue + ReadByConstReference: by const&.
static_assert(std::is_same_v<decltype(&T::bag_count), uint64_t (*)(const Bag &)>);
// CopyComponents/ReadByComponents: by value when the component is...
static_assert(std::is_same_v<decltype(&T::cell_flag), bool (*)(std::array<bool, 1>)>);
// ...and by const& when it is not.
static_assert(std::is_same_v<decltype(&T::cell_bag_count),
                             uint64_t (*)(const std::array<Bag, 1> &)>);

static int failures = 0;

static void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAIL: " << what << "\n";
    ++failures;
  }
}

int main() {
  check(T::flag_both(true, true) && !T::flag_both(true, false) && !T::flag_both(false, true),
        "flag_both");
  check(T::bag_count(Bag{}) == 0 && T::bag_count(Bag{7}) == 7, "bag_count");
  check(T::cell_flag({true}) && !T::cell_flag({false}), "cell_flag");
  check(T::cell_bag_count(T::make_cell(5)) == 5, "cell_bag_count");
  check(T::cell_bag_count({Bag{}}) == 0, "cell_bag_count empty");
  check(T::flag_of_option(std::optional<bool>{true}) && !T::flag_of_option(std::nullopt),
        "flag_of_option");
  check(T::bag_of_option(std::optional<uint64_t>{3}) == Bag{3}, "bag_of_option Some");
  check(T::bag_of_option(std::nullopt).empty(), "bag_of_option None");
  if (failures == 0) {
    std::cout << "All typed_mapping_copy tests passed!\n";
    return 0;
  }
  return 1;
}
