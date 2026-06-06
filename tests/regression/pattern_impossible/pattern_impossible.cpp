#include "pattern_impossible.h"

uint64_t PatternImpossible::complex_match(PatternImpossible::Three x) {
  switch (x) {
  case Three::ONE: {
    return UINT64_C(1);
  }
  case Three::TWO: {
    return UINT64_C(2);
  }
  case Three::THREE: {
    return UINT64_C(3);
  }
  default:
    std::unreachable();
  }
}

uint64_t PatternImpossible::nested_match(const PatternImpossible::nested &n) {
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
        return UINT64_C(0);
      }
    } else {
      return UINT64_C(0);
    }
  }
}

uint64_t PatternImpossible::double_match(PatternImpossible::Three x,
                                         PatternImpossible::Three y) {
  switch (x) {
  case Three::ONE: {
    switch (y) {
    case Three::ONE: {
      return UINT64_C(1);
    }
    case Three::TWO: {
      return UINT64_C(2);
    }
    case Three::THREE: {
      return UINT64_C(3);
    }
    default:
      std::unreachable();
    }
    break;
  }
  case Three::TWO: {
    return UINT64_C(10);
  }
  case Three::THREE: {
    return UINT64_C(20);
  }
  default:
    std::unreachable();
  }
}

uint64_t
PatternImpossible::multi_arg_pattern(const PatternImpossible::nested &n) {
  if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(n.v())) {
    return UINT64_C(0);
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
        return UINT64_C(0);
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
            return UINT64_C(0);
          }
        } else {
          return UINT64_C(0);
        }
      }
    } else {
      return UINT64_C(0);
    }
  }
}
