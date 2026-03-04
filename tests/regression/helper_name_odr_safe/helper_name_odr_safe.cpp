#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <helper_name_odr_safe.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int HelperNameOdrSafe::helper_a(const unsigned int n) {
  return std::move(n);
}

unsigned int HelperNameOdrSafe::helper_b(const unsigned int n) {
  return (std::move(n) + 1);
}
