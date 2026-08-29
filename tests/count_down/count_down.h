#ifndef INCLUDED_COUNT_DOWN
#define INCLUDED_COUNT_DOWN

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <utility>
#include <variant>

using namespace std::string_literals;

enum class Comparison { EQ, LT, GT };

struct CountDown {
  static void count_down(uint64_t n);
  static void two_prints(uint64_t n);
  static void echo_loop(uint64_t n);
  static void announce(uint64_t n);
  static void repeat_msg(uint64_t n, std::string msg);
  static void run_fixpoint();
  static bool string_eq(std::string s1, std::string s2);
  static void co_count_down();
  static void co_two_prints();
  static void co_echo_loop();
  static void co_announce(uint64_t round);
  static void co_repeat(std::string msg);
};

#endif // INCLUDED_COUNT_DOWN
