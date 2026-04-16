#ifndef INCLUDED_UNIT_MONOSTATE_ERASE
#define INCLUDED_UNIT_MONOSTATE_ERASE

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

struct UnitMonostateErase {
  /// --- Example 1: sequenced if returning unit ---
  ///
  /// The if result has type itree ioE unit, but its value is discarded
  /// by ;;.  Crane should lower this to plain if control flow.
  static void seq_if(const bool b);
  /// --- Example 2: sequenced if where both branches are effects ---
  ///
  /// Both branches produce itree ioE unit.  Should be a plain if.
  static void seq_if_both(const bool b);
  /// --- Example 3: tail-position match returning unit ---
  ///
  /// A match on a custom type, all branches unit-typed, in tail
  /// position of a void function.
  enum class Color { e_RED, e_GREEN, e_BLUE };

  template <typename T1>
  static T1 color_rect(const T1 f, const T1 f0, const T1 f1, const Color c) {
    switch (c) {
    case Color::e_RED: {
      return f;
    }
    case Color::e_GREEN: {
      return f0;
    }
    case Color::e_BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1>
  static T1 color_rec(const T1 f, const T1 f0, const T1 f1, const Color c) {
    switch (c) {
    case Color::e_RED: {
      return f;
    }
    case Color::e_GREEN: {
      return f0;
    }
    case Color::e_BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static void match_unit_tail(const Color c);
  /// --- Example 4: match inside bind ---
  static void match_then_next(const Color c);
  /// --- Example 5: chained sequenced ifs ---
  static void chained_ifs(const bool b1, const bool b2);
  /// --- Example 6: nested match-in-match ---
  static void nested_matches(const Color c1, const Color c2);
};

#endif // INCLUDED_UNIT_MONOSTATE_ERASE
