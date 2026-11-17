#ifndef INCLUDED_RECORD_DESTRUCTURE_ONCE_EXPR
#define INCLUDED_RECORD_DESTRUCTURE_ONCE_EXPR

#include <cstdint>
#include <utility>

struct RecordDestructureOnceExpr {
  struct triple {
    uint64_t t_steps;
    uint64_t t_twice;
    uint64_t t_zero;
  };

  static triple count(uint64_t n);
  static inline const uint64_t r_steps = count(UINT64_C(40)).t_steps;
};

#endif // INCLUDED_RECORD_DESTRUCTURE_ONCE_EXPR
