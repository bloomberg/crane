#ifndef INCLUDED_LET_MATCH_TYPE
#define INCLUDED_LET_MATCH_TYPE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <system_error>
#include <utility>
#include <variant>

struct LetMatchType {
  static uint64_t let_match_nat(bool b);
  static std::string let_match_string(uint64_t n);
  static uint64_t let_match_option(const std::optional<uint64_t> &o);
  static uint64_t let_nested_bool(bool a, bool b);
  static uint64_t multi_let_match(bool a, bool b);
  static uint64_t let_match_in_arg(uint64_t n);
  static std::string let_match_monadic(bool b);
  enum class Direction { NORTH, SOUTH, EAST, WEST };

  template <typename T1>
  static T1 direction_rect(T1 f, T1 f0, T1 f1, T1 f2, Direction d) {
    switch (d) {
    case Direction::NORTH: {
      return f;
    }
    case Direction::SOUTH: {
      return f0;
    }
    case Direction::EAST: {
      return f1;
    }
    case Direction::WEST: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 direction_rec(T1 f, T1 f0, T1 f1, T1 f2, Direction d) {
    switch (d) {
    case Direction::NORTH: {
      return f;
    }
    case Direction::SOUTH: {
      return f0;
    }
    case Direction::EAST: {
      return f1;
    }
    case Direction::WEST: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  static std::pair<uint64_t, uint64_t> direction_offset(Direction d);
};

#endif // INCLUDED_LET_MATCH_TYPE
