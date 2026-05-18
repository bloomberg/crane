#ifndef INCLUDED_PING_PONG
#define INCLUDED_PING_PONG

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <variant>

using namespace std::string_literals;

enum class Comparison { EQ, LT, GT };

struct PingPong {
  /// Check if two strings are equal using PrimString.compare.
  static bool string_eq(std::string s1, std::string s2);
  static void run_game(uint64_t round);
  /// Entry point.
  static void play();
};

#endif // INCLUDED_PING_PONG
