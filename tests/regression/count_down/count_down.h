#ifndef INCLUDED_COUNT_DOWN
#define INCLUDED_COUNT_DOWN

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

struct CountDown {
  /// Single effect then recurse: effect ;; recursive_call
  static void count_down(const unsigned int &n);
  /// Two effects then recurse: effect ;; effect ;; recursive_call
  static void two_prints(const unsigned int &n);
  /// Read from user, echo back, then recurse
  static void echo_loop(const unsigned int &n);
  /// Effect in base case too: both branches do IO
  static void announce(const unsigned int &n);
  /// Multiple arguments: two nat params, recurse on first
  static void repeat_msg(const unsigned int &n, const std::string msg);
  static void run_fixpoint();
  /// Helper: compare two strings
  static bool string_eq(const std::string s1, const std::string s2);
  static void co_count_down();
  static void co_two_prints();
  static void co_echo_loop();
  static void co_announce(unsigned int round);
  static void co_repeat(const std::string msg);
};

#endif // INCLUDED_COUNT_DOWN
