#include "lambda.h"

uint64_t Lambda::simple_lambda(uint64_t x) { return x; }

uint64_t Lambda::multi_arg(uint64_t _x0, uint64_t _x1) { return (_x0 + _x1); }

uint64_t Lambda::nested_lambda(uint64_t x, uint64_t y, uint64_t z) {
  return (x + (y + z));
}

uint64_t Lambda::make_adder(uint64_t _x0, uint64_t _x1) { return (_x0 + _x1); }
