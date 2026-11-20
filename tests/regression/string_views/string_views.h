#pragma once

#include <crane_string.h>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>

struct StringViews {
  static int64_t size_of(std::string_view x0_);
  static std::string describe(const std::string &name, std::string greeting);
  static char initial(std::string_view s);
  static int64_t c_size(const std::string &x0_);
  static std::string nonempty_or(std::string s, std::string fallback);
  static std::string first_two(std::string_view s);
  static int64_t prefix_size(std::string_view s);
  /// A view borrowed from a temporary, read within the full expression
  /// that holds the temporary.
  static int64_t joined_prefix_size(const std::string &a, const std::string &b);
  static int64_t outer(const std::string &s);
};
