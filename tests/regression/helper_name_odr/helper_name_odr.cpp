#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <helper_name_odr.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int HelperNameOdr::class_(const bool b) {
  if (b) {
    return (0 + 1);
  } else {
    return 0;
  }
}

unsigned int HelperNameOdr::class_0(const bool b) {
  if (b) {
    return ((0 + 1) + 1);
  } else {
    return (((0 + 1) + 1) + 1);
  }
}
