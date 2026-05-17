#include "unit_monostate_erase.h"

/// --- Example 1: sequenced if returning unit ---
///
/// The if result has type itree ioE unit, but its value is discarded
/// by ;;.  Crane should lower this to plain if control flow.
void UnitMonostateErase::seq_if(bool b) {
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
void UnitMonostateErase::seq_if_both(bool b) {
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

void UnitMonostateErase::match_unit_tail(UnitMonostateErase::Color c) {
  {
    [&]() -> void {
      switch (c) {
      case Color::RED: {
        return;
      }
      case Color::GREEN: {
        std::cout << "green"s << '\n';
        return;
      }
      case Color::BLUE: {
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
void UnitMonostateErase::match_then_next(UnitMonostateErase::Color c) {
  [&]() -> void {
    switch (c) {
    case Color::RED: {
      return;
    }
    case Color::GREEN: {
      std::cout << "green"s << '\n';
      return;
    }
    case Color::BLUE: {
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
void UnitMonostateErase::chained_ifs(bool b1, bool b2) {
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
void UnitMonostateErase::nested_matches(UnitMonostateErase::Color c1,
                                        UnitMonostateErase::Color c2) {
  [&]() -> void {
    switch (c1) {
    case Color::RED: {
      return [&]() -> void {
        switch (c2) {
        case Color::RED: {
          std::cout << "RR"s << '\n';
          return;
        }
        case Color::GREEN: {
          std::cout << "RG"s << '\n';
          return;
        }
        case Color::BLUE: {
          return;
        }
        default:
          std::unreachable();
        }
      }();
    }
    case Color::GREEN: {
      std::cout << "G"s << '\n';
      return;
    }
    case Color::BLUE: {
      return;
    }
    default:
      std::unreachable();
    }
  }();
  std::cout << "end"s << '\n';
  return;
}
