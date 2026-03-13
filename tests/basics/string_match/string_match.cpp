#include <string_match.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) bool StringMatch::is_empty(const std::string s) {
  return s.length() == int64_t(0);
}
