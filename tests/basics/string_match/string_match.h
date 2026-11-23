#pragma once

#include <crane_string.h>
#include <cstdint>
#include <string>
#include <string_view>

struct StringMatch {
  static inline const std::string str_empty = "";
  static inline const std::string str_hello = "hello";
  static inline const std::string str_world = "world";
  static inline const std::string str_cat =
      crane::string_capped(std::string("hello ") + std::string("world"));
  static inline const int64_t str_len_empty =
      static_cast<int64_t>(std::string_view("").size());
  static inline const int64_t str_len_hello =
      static_cast<int64_t>(std::string_view("hello").size());
  static bool is_empty(std::string_view s);
  static inline const bool test_empty_true = is_empty(std::string_view(""));
  static inline const bool test_empty_false = is_empty(std::string_view("x"));
  static inline const std::string test_cat =
      crane::string_capped(std::string("foo") + std::string("bar"));
};
