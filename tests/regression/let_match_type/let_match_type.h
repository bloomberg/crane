#ifndef INCLUDED_LET_MATCH_TYPE
#define INCLUDED_LET_MATCH_TYPE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LetMatchType {
  /// 1. let-bound bool match returning nat
  __attribute__((pure)) static unsigned int let_match_nat(const bool &b);
  /// 2. let-bound nat match returning string — TRIGGERS std::any bug
  __attribute__((pure)) static std::string
  let_match_string(const unsigned int &n);
  /// 3. let-bound option match
  __attribute__((pure)) static unsigned int
  let_match_option(const std::optional<unsigned int> &o);
  /// 4. let-bound nested bool match
  __attribute__((pure)) static unsigned int let_nested_bool(const bool &a,
                                                            const bool &b);
  /// 5. Multiple let-bound matches
  __attribute__((pure)) static unsigned int multi_let_match(const bool &a,
                                                            const bool &b);
  /// 6. let-bound match used in function argument
  __attribute__((pure)) static unsigned int
  let_match_in_arg(const unsigned int &n);
  /// 7. let-bound match in monadic context
  static std::string let_match_monadic(const bool &b);
  /// 8. let-bound match of custom type
  enum class Direction { e_NORTH, e_SOUTH, e_EAST, e_WEST };

  template <typename T1>
  static T1 direction_rect(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                           const Direction d) {
    switch (d) {
    case Direction::e_NORTH: {
      return f;
    }
    case Direction::e_SOUTH: {
      return f0;
    }
    case Direction::e_EAST: {
      return f1;
    }
    case Direction::e_WEST: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 direction_rec(const T1 f, const T1 f0, const T1 f1, const T1 f2,
                          const Direction d) {
    switch (d) {
    case Direction::e_NORTH: {
      return f;
    }
    case Direction::e_SOUTH: {
      return f0;
    }
    case Direction::e_EAST: {
      return f1;
    }
    case Direction::e_WEST: {
      return f2;
    }
    default:
      std::unreachable();
    }
  }

  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  direction_offset(const Direction d);
};

#endif // INCLUDED_LET_MATCH_TYPE
