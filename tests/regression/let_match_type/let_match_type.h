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
  static unsigned int let_match_nat(bool b);
  /// 2. let-bound nat match returning string — TRIGGERS std::any bug
  static std::string let_match_string(unsigned int n);
  /// 3. let-bound option match
  static unsigned int let_match_option(const std::optional<unsigned int> &o);
  /// 4. let-bound nested bool match
  static unsigned int let_nested_bool(bool a, bool b);
  /// 5. Multiple let-bound matches
  static unsigned int multi_let_match(bool a, bool b);
  /// 6. let-bound match used in function argument
  static unsigned int let_match_in_arg(unsigned int n);
  /// 7. let-bound match in monadic context
  static std::string let_match_monadic(bool b);
  /// 8. let-bound match of custom type
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

  static std::pair<unsigned int, unsigned int> direction_offset(Direction d);
};

#endif // INCLUDED_LET_MATCH_TYPE
