#pragma once

#include <cstdint>
#include <variant>

struct TickE;

struct ItreeTwoSelfCalls {
  /// Visits the midpoints of l..r, left half first; fuel bounds the
  /// depth.
  static void walk(uint64_t fuel, uint64_t l, uint64_t r);
  static void run(uint64_t n);
};

struct TickE {
  // DATA
  uint64_t n;

  // ACCESSORS
  TickE clone() const { return {n}; }

  // CREATORS
  static TickE tick(uint64_t n) { return {n}; }
};
