#ifndef INCLUDED_UNIT_MONOSTATE_ERASE
#define INCLUDED_UNIT_MONOSTATE_ERASE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct UnitMonostateErase {
  static void seq_if(bool b);
  static void seq_if_both(bool b);
  enum class Color { RED, GREEN, BLUE };

  template <typename T1> static T1 color_rect(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 color_rec(T1 f, T1 f0, T1 f1, Color c) {
    switch (c) {
    case Color::RED: {
      return f;
    }
    case Color::GREEN: {
      return f0;
    }
    case Color::BLUE: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static void match_unit_tail(Color c);
  static void match_then_next(Color c);
  static void chained_ifs(bool b1, bool b2);
  static void nested_matches(Color c1, Color c2);
};

#endif // INCLUDED_UNIT_MONOSTATE_ERASE
