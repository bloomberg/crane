#include "record_destructure_once.h"

RecordDestructureOnce::triple RecordDestructureOnce::count(uint64_t n) {
  if (n <= 0) {
    return triple{UINT64_C(0), UINT64_C(0), UINT64_C(0)};
  } else {
    uint64_t m = n - 1;
    auto _cs = count(m);
    uint64_t a = std::move(_cs).t_steps;
    uint64_t b = std::move(_cs).t_twice;
    uint64_t c = std::move(_cs).t_zero;
    return triple{(a + 1), (b + UINT64_C(2)), c};
  }
}
