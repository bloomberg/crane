#include "callable_crossing_matrix.h"

uint64_t CallableCrossingMatrix::add2(uint64_t x0_, uint64_t x1_) {
  return x0_ + x1_;
}

uint64_t CallableCrossingMatrix::add3(uint64_t a, uint64_t b, uint64_t c) {
  return a + b + c;
}

/// Sources.
uint64_t CallableCrossingMatrix::curried2(uint64_t x0_, uint64_t x1_) {
  return x0_ + x1_;
}

uint64_t CallableCrossingMatrix::curried3(uint64_t a, uint64_t b, uint64_t c) {
  return add3(a, b, c);
}

uint64_t CallableCrossingMatrix::src_lambda2(uint64_t x0_, uint64_t x1_) {
  return x0_ + x1_;
}

uint64_t CallableCrossingMatrix::src_let2(uint64_t n, uint64_t a, uint64_t b) {
  return a + b + n;
}

uint64_t CallableCrossingMatrix::src_match2(uint64_t n, uint64_t x0_,
                                            uint64_t x1_) {
  if (n <= 0) {
    return add2(x0_, x1_);
  } else {
    uint64_t _x = n - 1;
    return x1_ + x0_;
  }
}

uint64_t CallableCrossingMatrix::src_fix2(uint64_t m, uint64_t a, uint64_t b) {
  if (m <= 0) {
    return a + b;
  } else {
    uint64_t m_ = m - 1;
    return src_fix2(m_, a, b);
  }
}

uint64_t CallableCrossingMatrix::src_fix3(uint64_t m, uint64_t a, uint64_t b,
                                          uint64_t c) {
  if (m <= 0) {
    return a + b + c;
  } else {
    uint64_t m_ = m - 1;
    return src_fix3(m_, a, b, c);
  }
}

uint64_t CallableCrossingMatrix::src_mapping2(uint64_t x0_, uint64_t x1_) {
  return crane::fn<uint64_t(uint64_t, uint64_t)>(add2)(x0_, x1_);
}
