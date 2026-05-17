#ifndef INCLUDED_COUNT_DOWN
#define INCLUDED_COUNT_DOWN

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <variant>

using namespace std::string_literals;

enum class Comparison { EQ, LT, GT };

struct CountDown {
  /// Single effect then recurse: effect ;; recursive_call
  static void count_down(unsigned int n);
  /// Two effects then recurse: effect ;; effect ;; recursive_call
  static void two_prints(unsigned int n);
  /// Read from user, echo back, then recurse
  static void echo_loop(unsigned int n);
  /// Effect in base case too: both branches do IO
  static void announce(unsigned int n);
  /// Multiple arguments: two nat params, recurse on first
  static void repeat_msg(unsigned int n, std::string msg);
  static void run_fixpoint();
  /// Helper: compare two strings
  static bool string_eq(std::string s1, std::string s2);
  static void co_count_down();
  static void co_two_prints();
  static void co_echo_loop();
  static void co_announce(unsigned int round);
  static void co_repeat(std::string msg);
};

#endif // INCLUDED_COUNT_DOWN
