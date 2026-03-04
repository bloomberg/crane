#include <algorithm>
#include <any>
#include <bool_nat_ternary_precedence_safe.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int BoolNatTernaryPrecedenceSafe::branch_left(const bool b) {
  if (b) {
    return (0 + 1);
  } else {
    return 0;
  }
}

unsigned int BoolNatTernaryPrecedenceSafe::branch_right(const bool b) {
  if (b) {
    return ((0 + 1) + 1);
  } else {
    return (((0 + 1) + 1) + 1);
  }
}
