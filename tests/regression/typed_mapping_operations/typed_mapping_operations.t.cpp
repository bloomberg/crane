// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Operation mappings: values, single evaluation in source order, and the
// passing a contract asks for (Take owns, Read and Write borrow).  The
// diagnostics are checked while the .vo is built.
#include <typed_mapping_operations.h>

#include <cstdint>
#include <iostream>
#include <memory>
#include <type_traits>
#include <utility>
#include <vector>

using T = TypedMappingOperations;
using ops_support::buffer;

// Read borrows, Take owns, Write borrows.
static_assert(std::is_same_v<decltype(&T::size_of), uint64_t (*)(const buffer &)>);
static_assert(std::is_same_v<decltype(&T::push_one), buffer (*)(buffer)>);
static_assert(std::is_same_v<decltype(&T::push_keep),
                             std::pair<buffer, uint64_t> (*)(buffer)>);
static_assert(std::is_same_v<decltype(&T::checked_one), buffer (*)(buffer)>);
static_assert(std::is_same_v<decltype(&T::poke_twice),
                             uint64_t (*)(const std::shared_ptr<std::int64_t> &)>);
// The erased type parameter of box_push takes no argument: the Take is its
// buffer's.
static_assert(std::is_same_v<decltype(&T::box_push_one<int>),
                             std::vector<int> (*)(std::vector<int>, const int &)>);

static int failures = 0;

static void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAIL: " << what << "\n";
    ++failures;
  }
}

static bool traced(std::vector<std::uint64_t> expected) {
  bool ok = ops_support::trace() == expected;
  ops_support::trace().clear();
  return ok;
}

int main() {
  check(T::counted(5) == 7, "counted(5)");

  check(T::doubled(21) == 42, "doubled(21)");
  check(traced({21}), "doubled logs its argument once");

  // combine(tick 1, tick 2) splices the second argument first and the first
  // twice: each tick runs once, in source order.
  check(T::ordered(1, 2) == 121, "ordered(1, 2)");
  check(traced({1, 2}), "ordered ticks 1 then 2, once each");

  // An ignored argument with an effect is evaluated once and discarded; a
  // pure one is not evaluated.
  check(T::skipped(3, 4) == 5, "skipped(3, 4)");
  check(traced({3, 4}), "skipped ticks 3 then 4");
  check(T::skipped_pure(3, 4) == 5, "skipped_pure(3, 4)");
  check(traced({4}), "skipped_pure ticks 4 only");

  buffer b = ops_support::push(buffer{}, 7);
  check(T::size_of(b) == 1, "size_of");

  // Take: moved at its last use...
  ops_support::copies() = 0;
  buffer pushed = T::push_one(std::move(b));
  check(ops_support::copies() == 0, "push_one moves its buffer");
  check(pushed.items == std::vector<std::uint64_t>{7, 1}, "push_one value");

  // ... and copied where it is still live.
  ops_support::copies() = 0;
  auto kept = T::push_keep(std::move(pushed));
  check(ops_support::copies() == 1, "push_keep copies its live buffer once");
  check(kept.first.items == std::vector<std::uint64_t>{7, 1, 1},
        "push_keep pushed");
  check(kept.second == 2, "push_keep reads the original");

  ops_support::copies() = 0;
  buffer checked = T::checked_one(buffer{});
  check(ops_support::copies() == 0, "checked_one moves its buffer");
  check(checked.items == std::vector<std::uint64_t>{1}, "checked_one value");

  auto cell = std::make_shared<std::int64_t>(10);
  check(T::poke_twice(cell) == 13, "poke_twice");
  check(*cell == 13, "poke_twice writes through the handle");
  check(T::fresh_cell(9) == 9, "fresh_cell");

  check(T::boxed(3, true), "boxed");
  check(T::box_third(std::vector<int>{1, 2, 3}) == 3, "box_third");
  check(T::box_push_one(std::vector<int>{1}, 2) == std::vector<int>{1, 2},
        "box_push_one");

  if (failures == 0) {
    std::cout << "All typed_mapping_operations tests passed!\n";
    return 0;
  }
  return 1;
}
