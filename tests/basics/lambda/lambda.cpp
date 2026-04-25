#include <lambda.h>

#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int Lambda::simple_lambda(unsigned int x) {
  return x;
}

__attribute__((pure)) unsigned int Lambda::multi_arg(const unsigned int &_x0,
                                                     const unsigned int &_x1) {
  return (_x0 + _x1);
}

__attribute__((pure)) unsigned int
Lambda::nested_lambda(const unsigned int &x, const unsigned int &y,
                      const unsigned int &z) {
  return (x + (y + z));
}

__attribute__((pure)) unsigned int Lambda::make_adder(const unsigned int &_x0,
                                                      const unsigned int &_x1) {
  return (_x0 + _x1);
}
