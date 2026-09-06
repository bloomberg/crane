#include "lambda.h"

uint64_t Lambda::simple_lambda(uint64_t x) { return x; }

uint64_t Lambda::multi_arg(uint64_t x0_, uint64_t x1_) { return (x0_ + x1_); }

uint64_t Lambda::nested_lambda(uint64_t x, uint64_t y, uint64_t z) {
  return (x + (y + z));
}

uint64_t Lambda::make_adder(uint64_t x0_, uint64_t x1_) { return (x0_ + x1_); }
