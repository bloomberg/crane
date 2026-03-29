#include <higher_order.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// adder n returns a function that adds n to its argument.
__attribute__((pure)) unsigned int HigherOrder::adder(const unsigned int _x0,
                                                      const unsigned int _x1) {
  return (_x0 + _x1);
}
