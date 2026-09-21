#ifndef INCLUDED_PARALLEL
#define INCLUDED_PARALLEL

#include <future>
#include <utility>

struct ParallelTest {
  static uint64_t ack(const std::pair<uint64_t, uint64_t> &p);
  static std::pair<uint64_t, uint64_t> fast(uint64_t m, uint64_t n);
  static std::pair<uint64_t, uint64_t> slow(uint64_t m, uint64_t n);
};

struct Nat {
  static inline const uint64_t one = UINT64_C(1);
};

#endif // INCLUDED_PARALLEL
