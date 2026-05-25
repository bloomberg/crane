#ifndef INCLUDED_LET_MATCH_TYPE
#define INCLUDED_LET_MATCH_TYPE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

struct LetMatchType {
  /// 1. let-bound bool match returning nat
  static uint64_t let_match_nat(bool b);
  /// 2. let-bound nat match returning string — TRIGGERS std::any bug
  static std::string let_match_string(uint64_t n);
  /// 3. let-bound option match
  static uint64_t let_match_option(const std::optional<uint64_t> &o);
  /// 4. let-bound nested bool match
  static uint64_t let_nested_bool(bool a, bool b);
  /// 5. Multiple let-bound matches
  static uint64_t multi_let_match(bool a, bool b);
  /// 6. let-bound match used in function argument
  static uint64_t let_match_in_arg(uint64_t n);
  /// 7. let-bound match in monadic context
  static std::string let_match_monadic(bool b);
  /// 8. let-bound match of custom type
  enum class Direction { NORTH, SOUTH, EAST, WEST };

  template <typename T1>
  static T1 direction_rect(T1 f, T1 f0, T1 f1, T1 f2, Direction d) {
    switch (d) {
    case Direction::NORTH: {
      return f;
    } break;
    case Direction::SOUTH: {
      return f0;
    } break;
    case Direction::EAST: {
      return f1;
    } break;
    case Direction::WEST: {
      return f2;
    } break;
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 direction_rec(T1 f, T1 f0, T1 f1, T1 f2, Direction d) {
    switch (d) {
    case Direction::NORTH: {
      return f;
    } break;
    case Direction::SOUTH: {
      return f0;
    } break;
    case Direction::EAST: {
      return f1;
    } break;
    case Direction::WEST: {
      return f2;
    } break;
    default:
      std::unreachable();
    }
  }

  static std::pair<uint64_t, uint64_t> direction_offset(Direction d);
};

#endif // INCLUDED_LET_MATCH_TYPE
