#ifndef INCLUDED_PING_PONG
#define INCLUDED_PING_PONG

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Comparison { e_EQ, e_LT, e_GT };

struct PingPong {
  /// Check if two strings are equal using PrimString.compare.
  __attribute__((pure)) static bool string_eq(const std::string s1,
                                              const std::string s2);
  static void run_game(const unsigned int round);
  /// Entry point.
  static void play();
};

#endif // INCLUDED_PING_PONG
