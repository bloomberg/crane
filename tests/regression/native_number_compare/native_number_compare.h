#pragma once

#include <cstdint>
#include <type_traits>
#include <utility>

enum class Comparison;

struct Nat {};

struct Pos {};

struct N {};

struct Z {};

enum class Comparison { EQ, LT, GT };

/// compare and eq_dec on numbers mapped to machine integers become
/// native comparisons.  The structural versions count both arguments down
/// to zero, so the large values in the test would take hours (compare)
/// or overflow the stack (eq_dec).
struct NativeNumberCompare {
  static uint64_t code(Comparison c);
  static uint64_t nat_cmp(uint64_t a, uint64_t b);
  static uint64_t nat_cmp_(uint64_t a, uint64_t b);
  static bool nat_dec(uint64_t a, uint64_t b);
  static uint64_t n_cmp(unsigned int a, unsigned int b);
  static bool n_dec(unsigned int a, unsigned int b);
  static uint64_t pos_cmp(unsigned int a, unsigned int b);
  static bool pos_dec(unsigned int a, unsigned int b);
  static uint64_t z_cmp(int64_t a, int64_t b);
  static bool z_dec(int64_t a, int64_t b);

  /// compare passed as a value rather than called.
  template <typename F0>
    requires std::is_invocable_r_v<Comparison, F0 &, uint64_t &, uint64_t &>
  static uint64_t apply_cmp(F0 &&f, uint64_t a, uint64_t b) {
    return code(f(a, b));
  }

  static uint64_t nat_cmp_value(uint64_t a, uint64_t b);
};
