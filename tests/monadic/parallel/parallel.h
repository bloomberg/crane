#ifndef INCLUDED_PARALLEL
#define INCLUDED_PARALLEL

#include "shared_block.h"
#include <cstdint>
#include <future>
#include <utility>
static_assert(crane::rc_is_atomic,
              "this unit spawns threads, but a header included before it chose "
              "CRANE_NON_ATOMIC_RC");

struct ParallelTest {
  static uint64_t ack(const std::pair<uint64_t, uint64_t> &p);
  static std::pair<uint64_t, uint64_t> fast(uint64_t m, uint64_t n);
  static std::pair<uint64_t, uint64_t> slow(uint64_t m, uint64_t n);
};

struct Nat {
  static constexpr uint64_t one = UINT64_C(1);
};

#endif // INCLUDED_PARALLEL
