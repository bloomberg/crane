#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <lambda.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int Lambda::simple_lambda(const unsigned int x) {
  return std::move(x);
}

unsigned int Lambda::multi_arg(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}

unsigned int Lambda::nested_lambda(const unsigned int x, const unsigned int y,
                                   const unsigned int z) {
  return (x + (y + z));
}

unsigned int Lambda::make_adder(const unsigned int _x0,
                                const unsigned int _x1) {
  return (_x0 + _x1);
}
