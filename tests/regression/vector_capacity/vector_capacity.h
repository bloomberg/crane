#ifndef INCLUDED_VECTOR_CAPACITY
#define INCLUDED_VECTOR_CAPACITY

#include <cstdint>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  static bool even(uint64_t n);
};

/// A fresh vector filled by a counted loop, one append per iteration, has
/// its capacity reserved from the loop's count; any other filling shape is
/// left to grow as it would.
struct VectorCapacity {
  /// Reserved: exactly n appends.
  static std::vector<uint64_t> fill(uint64_t n);
  /// Not reserved: the append is conditional.
  static std::vector<uint64_t> fill_even(uint64_t n);
  /// Not reserved: two appends an iteration.
  static std::vector<uint64_t> fill_twice(uint64_t n);
  /// Not reserved: the loop can stop early.
  static std::vector<uint64_t> fill_until_five(uint64_t n);
};

#endif // INCLUDED_VECTOR_CAPACITY
