#include <algorithm>
#include <any>
#include <bool_nat_ternary_precedence.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int BoolNatTernaryPrecedence::class_(const bool b) {
  if (b) {
    return (0 + 1);
  } else {
    return 0;
  }
}

unsigned int BoolNatTernaryPrecedence::class_0(const bool b) {
  if (b) {
    return ((0 + 1) + 1);
  } else {
    return (((0 + 1) + 1) + 1);
  }
}
