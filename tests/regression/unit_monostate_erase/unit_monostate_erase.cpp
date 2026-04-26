#include <unit_monostate_erase.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// --- Example 1: sequenced if returning unit ---
///
/// The if result has type itree ioE unit, but its value is discarded
/// by ;;.  Crane should lower this to plain if control flow.
void UnitMonostateErase::seq_if(const bool &b) {
  [&]() -> void {
    if (b) {
      std::cout << "yes"s << '\n';
      return;
    } else {
      return;
    }
  }();
  std::cout << "done"s << '\n';
  return;
}

/// --- Example 2: sequenced if where both branches are effects ---
///
/// Both branches produce itree ioE unit.  Should be a plain if.
void UnitMonostateErase::seq_if_both(const bool &b) {
  [&]() -> void {
    if (b) {
      std::cout << "A"s << '\n';
      return;
    } else {
      std::cout << "B"s << '\n';
      return;
    }
  }();
  std::cout << "done"s << '\n';
  return;
}

void UnitMonostateErase::match_unit_tail(const UnitMonostateErase::Color c) {
  {
    [&]() -> void {
      switch (c) {
      case Color::e_RED: {
        return;
      }
      case Color::e_GREEN: {
        std::cout << "green"s << '\n';
        return;
      }
      case Color::e_BLUE: {
        std::cout << "blue"s << '\n';
        return;
      }
      default:
        std::unreachable();
      }
    }();
    return;
  }
}

/// --- Example 4: match inside bind ---
void UnitMonostateErase::match_then_next(const UnitMonostateErase::Color c) {
  [&]() -> void {
    switch (c) {
    case Color::e_RED: {
      return;
    }
    case Color::e_GREEN: {
      std::cout << "green"s << '\n';
      return;
    }
    case Color::e_BLUE: {
      std::cout << "blue"s << '\n';
      return;
    }
    default:
      std::unreachable();
    }
  }();
  std::cout << "after match"s << '\n';
  return;
}

/// --- Example 5: chained sequenced ifs ---
void UnitMonostateErase::chained_ifs(const bool &b1, bool b2) {
  [&]() -> void {
    if (b1) {
      std::cout << "b1"s << '\n';
      return;
    } else {
      return;
    }
  }();
  [&]() -> void {
    if (b2) {
      std::cout << "b2"s << '\n';
      return;
    } else {
      return;
    }
  }();
  std::cout << "end"s << '\n';
  return;
}

/// --- Example 6: nested match-in-match ---
void UnitMonostateErase::nested_matches(const UnitMonostateErase::Color c1,
                                        const UnitMonostateErase::Color c2) {
  [&]() -> void {
    switch (c1) {
    case Color::e_RED: {
      return [&]() -> void {
        switch (c2) {
        case Color::e_RED: {
          std::cout << "RR"s << '\n';
          return;
        }
        case Color::e_GREEN: {
          std::cout << "RG"s << '\n';
          return;
        }
        case Color::e_BLUE: {
          return;
        }
        default:
          std::unreachable();
        }
      }();
    }
    case Color::e_GREEN: {
      std::cout << "G"s << '\n';
      return;
    }
    case Color::e_BLUE: {
      return;
    }
    default:
      std::unreachable();
    }
  }();
  std::cout << "end"s << '\n';
  return;
}
