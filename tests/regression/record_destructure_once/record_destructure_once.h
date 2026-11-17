#ifndef INCLUDED_RECORD_DESTRUCTURE_ONCE
#define INCLUDED_RECORD_DESTRUCTURE_ONCE

#include <cstdint>
#include <utility>

struct RecordDestructureOnce {
  struct triple {
    uint64_t t_steps;
    uint64_t t_twice;
    uint64_t t_zero;
  };

  static triple count(uint64_t n);
  static inline const uint64_t r_steps = count(UINT64_C(40)).t_steps;
  static inline const uint64_t r_twice = count(UINT64_C(40)).t_twice;
  static inline const uint64_t r_zero = count(UINT64_C(40)).t_zero;
};

#endif // INCLUDED_RECORD_DESTRUCTURE_ONCE
