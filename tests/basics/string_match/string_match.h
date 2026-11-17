#ifndef INCLUDED_STRING_MATCH
#define INCLUDED_STRING_MATCH

#include <cstdint>
#include <string>
#include <utility>

struct StringMatch {
  static inline const std::string str_empty = "";
  static inline const std::string str_hello = "hello";
  static inline const std::string str_world = "world";
  static inline const std::string str_cat =
      std::string("hello ") + std::string("world");
  static inline const int64_t str_len_empty =
      static_cast<int64_t>(std::string("").length());
  static inline const int64_t str_len_hello =
      static_cast<int64_t>(std::string("hello").length());
  static bool is_empty(std::string s);
  static inline const bool test_empty_true = is_empty("");
  static inline const bool test_empty_false = is_empty("x");
  static inline const std::string test_cat =
      std::string("foo") + std::string("bar");
};

#endif // INCLUDED_STRING_MATCH
