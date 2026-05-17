#include "pattern_impossible.h"

unsigned int PatternImpossible::complex_match(PatternImpossible::Three x) {
  switch (x) {
  case Three::ONE: {
    return 1u;
  }
  case Three::TWO: {
    return 2u;
  }
  case Three::THREE: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}

unsigned int
PatternImpossible::nested_match(const PatternImpossible::nested &n) {
  if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(n.v())) {
    const auto &[a0] =
        std::get<typename PatternImpossible::nested::Leaf>(n.v());
    return a0;
  } else {
    const auto &[a0, a1] =
        std::get<typename PatternImpossible::nested::Node>(n.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            _sv0.v())) {
      const auto &[a00] =
          std::get<typename PatternImpossible::nested::Leaf>(_sv0.v());
      auto &&_sv1 = *a1;
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              _sv1.v())) {
        const auto &[a01] =
            std::get<typename PatternImpossible::nested::Leaf>(_sv1.v());
        return (a00 + a01);
      } else {
        return 0u;
      }
    } else {
      return 0u;
    }
  }
}

unsigned int PatternImpossible::double_match(PatternImpossible::Three x,
                                             PatternImpossible::Three y) {
  switch (x) {
  case Three::ONE: {
    switch (y) {
    case Three::ONE: {
      return 1u;
    }
    case Three::TWO: {
      return 2u;
    }
    case Three::THREE: {
      return 3u;
    }
    default:
      std::unreachable();
    }
  }
  case Three::TWO: {
    return 10u;
  }
  case Three::THREE: {
    return 20u;
  }
  default:
    std::unreachable();
  }
}

unsigned int
PatternImpossible::multi_arg_pattern(const PatternImpossible::nested &n) {
  if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(n.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] =
        std::get<typename PatternImpossible::nested::Node>(n.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            _sv0.v())) {
      const auto &[a00] =
          std::get<typename PatternImpossible::nested::Leaf>(_sv0.v());
      auto &&_sv1 = *a1;
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              _sv1.v())) {
        return 0u;
      } else {
        const auto &[a01, a11] =
            std::get<typename PatternImpossible::nested::Node>(_sv1.v());
        auto &&_sv2 = *a01;
        if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                _sv2.v())) {
          const auto &[a02] =
              std::get<typename PatternImpossible::nested::Leaf>(_sv2.v());
          auto &&_sv3 = *a11;
          if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                  _sv3.v())) {
            const auto &[a03] =
                std::get<typename PatternImpossible::nested::Leaf>(_sv3.v());
            return ((a00 + a02) + a03);
          } else {
            return 0u;
          }
        } else {
          return 0u;
        }
      }
    } else {
      return 0u;
    }
  }
}
