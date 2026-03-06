#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <higher_order.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int HigherOrder::adder(const unsigned int _x0,
                                const unsigned int _x1) {
  return (_x0 + _x1);
}
