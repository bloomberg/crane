#include "lambda_capture_perf.h"

List<unsigned int> LambdaCapturePerf::iota(unsigned int n) {
  if (n <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int n_ = n - 1;
    return List<unsigned int>::cons(n_, iota(n_));
  }
}
