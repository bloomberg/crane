#include "lambda.h"

unsigned int Lambda::simple_lambda(unsigned int x) { return x; }

unsigned int Lambda::multi_arg(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int Lambda::nested_lambda(unsigned int x, unsigned int y,
                                   unsigned int z) {
  return (x + (y + z));
}

unsigned int Lambda::make_adder(unsigned int _x0, unsigned int _x1) {
  return (_x0 + _x1);
}
