#pragma once

#include <cstdint>
#include <iostream>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

enum class Comparison;
enum class Comparison { EQ, LT, GT };

struct PingPong {
  /// Check if two strings are equal using PrimString.compare.
  static bool string_eq(std::string_view s1, std::string_view s2);
  static void run_game(uint64_t round);
  /// Entry point.
  static void play();
};
