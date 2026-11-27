#pragma once

#include <cstddef>
#include <cstdint>
#include <cstring>
#include <string>
#include <string_view>

struct StringViews {
  static int64_t size_of(std::string_view x0_);
  static std::string describe(const std::string &name, std::string greeting);
  static int64_t initial(std::string_view s);
  static int64_t c_size(const std::string &x0_);
  static std::string nonempty_or(std::string s, std::string fallback);
  static std::string first_two(std::string_view s);
  static int64_t prefix_size(std::string_view s);
  /// A view borrowed from a temporary, read within the full expression
  /// that holds the temporary.
  static int64_t joined_prefix_size(const std::string &a, const std::string &b);
  static int64_t outer(const std::string &s);
  /// String literals read as views: the view of the literal itself, with
  /// no std::string made for it; one holding a NUL carries its length.
  static inline const int64_t literal_size = size_of(std::string_view("hello"));
  static inline const int64_t literal_length =
      static_cast<int64_t>(std::string_view("abc").size());
  static inline const int64_t literal_prefix_size = static_cast<int64_t>(
      (std::string_view("crane").substr(0, INT64_C(3))).size());
  static inline const std::string with_nul = std::string("a\000b", 3);
  static inline const int64_t nul_size = size_of(std::string_view("a\000b", 3));
  static inline const int64_t nul_length =
      static_cast<int64_t>(std::string_view("a\000b", 3).size());
};
