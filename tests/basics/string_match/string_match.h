#ifndef INCLUDED_STRING_MATCH
#define INCLUDED_STRING_MATCH

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

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct StringMatch {
  static inline const std::string str_empty = "";
  static inline const std::string str_hello = "hello";
  static inline const std::string str_world = "world";
  static inline const std::string str_cat = "hello "s + "world"s;
  static inline const int64_t str_len_empty = ""s.length();
  static inline const int64_t str_len_hello = "hello"s.length();
  __attribute__((pure)) static bool is_empty(const std::string s);
  static inline const bool test_empty_true = is_empty("");
  static inline const bool test_empty_false = is_empty("x");
  static inline const std::string test_cat = "foo"s + "bar"s;
};

#endif // INCLUDED_STRING_MATCH
