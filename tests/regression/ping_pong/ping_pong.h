#ifndef INCLUDED_PING_PONG
#define INCLUDED_PING_PONG

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Comparison { e_EQ, e_LT, e_GT };

struct PingPong {
  /// Check if two strings are equal using PrimString.compare.
  static bool string_eq(const std::string s1, const std::string s2);
  static void run_game(unsigned int round);
  /// Entry point.
  static void play();
};

#endif // INCLUDED_PING_PONG
