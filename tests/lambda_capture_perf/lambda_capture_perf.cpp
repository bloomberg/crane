#include "lambda_capture_perf.h"

List<uint64_t> LambdaCapturePerf::iota(uint64_t n) {
  if (n <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t n_ = n - 1;
    return List<uint64_t>::cons(n_, iota(n_));
  }
}
