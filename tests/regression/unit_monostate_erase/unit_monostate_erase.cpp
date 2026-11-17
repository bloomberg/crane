#include "unit_monostate_erase.h"

/// --- Example 1: sequenced if returning unit ---
///
/// The if result has type itree ioE unit, but its value is discarded
/// by ;;.  Crane should lower this to plain if control flow.
void UnitMonostateErase::seq_if(bool b) {
  [&]() -> void {
    if (b) {
      std::cout << std::string("yes") << '\n';
      return;
    } else {
      return;
    }
  }();
  std::cout << std::string("done") << '\n';
  return;
}

/// --- Example 2: sequenced if where both branches are effects ---
///
/// Both branches produce itree ioE unit.  Should be a plain if.
void UnitMonostateErase::seq_if_both(bool b) {
  [&]() -> void {
    if (b) {
      std::cout << std::string("A") << '\n';
      return;
    } else {
      std::cout << std::string("B") << '\n';
      return;
    }
  }();
  std::cout << std::string("done") << '\n';
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
        std::cout << std::string("green") << '\n';
        return;
      }
      case Color::BLUE: {
        std::cout << std::string("blue") << '\n';
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
      std::cout << std::string("green") << '\n';
      return;
    }
    case Color::BLUE: {
      std::cout << std::string("blue") << '\n';
      return;
    }
    default:
      std::unreachable();
    }
  }();
  std::cout << std::string("after match") << '\n';
  return;
}

/// --- Example 5: chained sequenced ifs ---
void UnitMonostateErase::chained_ifs(bool b1, bool b2) {
  [&]() -> void {
    if (b1) {
      std::cout << std::string("b1") << '\n';
      return;
    } else {
      return;
    }
  }();
  [&]() -> void {
    if (b2) {
      std::cout << std::string("b2") << '\n';
      return;
    } else {
      return;
    }
  }();
  std::cout << std::string("end") << '\n';
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
          std::cout << std::string("RR") << '\n';
          return;
        }
        case Color::GREEN: {
          std::cout << std::string("RG") << '\n';
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
      std::cout << std::string("G") << '\n';
      return;
    }
    case Color::BLUE: {
      return;
    }
    default:
      std::unreachable();
    }
  }();
  std::cout << std::string("end") << '\n';
  return;
}
