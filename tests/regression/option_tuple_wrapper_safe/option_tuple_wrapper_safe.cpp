#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <option_tuple_wrapper_safe.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int OptionTupleWrapperSafe::pick_nat(const bool b) {
  if (b) {
    return (0 + 1);
  } else {
    return 0;
  }
}
