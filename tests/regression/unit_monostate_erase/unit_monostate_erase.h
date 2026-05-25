#ifndef INCLUDED_UNIT_MONOSTATE_ERASE
#define INCLUDED_UNIT_MONOSTATE_ERASE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct UnitMonostateErase {
  /// --- Example 1: sequenced if returning unit ---
  ///
  /// The if result has type itree ioE unit, but its value is discarded
  /// by ;;.  Crane should lower this to plain if control flow.
  static void seq_if(bool b);
  /// --- Example 2: sequenced if where both branches are effects ---
  ///
  /// Both branches produce itree ioE unit.  Should be a plain if.
  static void seq_if_both(bool b);
  /// --- Example 3: tail-position match returning unit ---
  ///
  /// A match on a custom type, all branches unit-typed, in tail
  /// position of a void function.
  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    } break;
    case Color::GREEN: {
      return f0;
    } break;
    case Color::BLUE: {
      return f1;
    } break;
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    } break;
    case Color::GREEN: {
      return f0;
    } break;
    case Color::BLUE: {
      return f1;
    } break;
    default:
      std::unreachable();
    }
  }

  static void match_unit_tail(Color c);
  /// --- Example 4: match inside bind ---
  static void match_then_next(Color c);
  /// --- Example 5: chained sequenced ifs ---
  static void chained_ifs(bool b1, bool b2);
  /// --- Example 6: nested match-in-match ---
  static void nested_matches(Color c1, Color c2);
};

#endif // INCLUDED_UNIT_MONOSTATE_ERASE
