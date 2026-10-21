#include "record_destructure_once_expr.h"

RecordDestructureOnceExpr::triple RecordDestructureOnceExpr::count(uint64_t n) {
  if (n <= 0) {
    return triple{UINT64_C(0), UINT64_C(0), UINT64_C(0)};
  } else {
    uint64_t m = n - 1;
    return triple{[&]() {
                    auto _cs = count(m);
                    uint64_t a = std::move(_cs).t_steps;
                    uint64_t b = std::move(_cs).t_twice;
                    uint64_t c = std::move(_cs).t_zero;
                    return (((a + b) + c) + 1);
                  }(),
                  UINT64_C(0), UINT64_C(0)};
  }
}
