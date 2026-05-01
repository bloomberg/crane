#include <pattern_impossible.h>

unsigned int
PatternImpossible::complex_match(const PatternImpossible::Three x) {
  switch (x) {
  case Three::e_ONE: {
    return 1u;
  }
  case Three::e_TWO: {
    return 2u;
  }
  case Three::e_THREE0: {
    return 3u;
  }
  default:
    std::unreachable();
  }
}

unsigned int
PatternImpossible::nested_match(const PatternImpossible::nested &n) {
  if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(n.v())) {
    const auto &[d_a0] =
        std::get<typename PatternImpossible::nested::Leaf>(n.v());
    return d_a0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename PatternImpossible::nested::Node>(n.v());
    auto &&_sv0 = *(d_a0);
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            _sv0.v())) {
      const auto &[d_a00] =
          std::get<typename PatternImpossible::nested::Leaf>(_sv0.v());
      auto &&_sv1 = *(d_a1);
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              _sv1.v())) {
        const auto &[d_a01] =
            std::get<typename PatternImpossible::nested::Leaf>(_sv1.v());
        return (d_a00 + d_a01);
      } else {
        return 0u;
      }
    } else {
      return 0u;
    }
  }
}

unsigned int PatternImpossible::double_match(const PatternImpossible::Three x,
                                             const PatternImpossible::Three y) {
  switch (x) {
  case Three::e_ONE: {
    switch (y) {
    case Three::e_ONE: {
      return 1u;
    }
    case Three::e_TWO: {
      return 2u;
    }
    case Three::e_THREE0: {
      return 3u;
    }
    default:
      std::unreachable();
    }
  }
  case Three::e_TWO: {
    return 10u;
  }
  case Three::e_THREE0: {
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
    const auto &[d_a0, d_a1] =
        std::get<typename PatternImpossible::nested::Node>(n.v());
    auto &&_sv0 = *(d_a0);
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            _sv0.v())) {
      const auto &[d_a00] =
          std::get<typename PatternImpossible::nested::Leaf>(_sv0.v());
      auto &&_sv1 = *(d_a1);
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              _sv1.v())) {
        return 0u;
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename PatternImpossible::nested::Node>(_sv1.v());
        auto &&_sv2 = *(d_a01);
        if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                _sv2.v())) {
          const auto &[d_a02] =
              std::get<typename PatternImpossible::nested::Leaf>(_sv2.v());
          auto &&_sv3 = *(d_a11);
          if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                  _sv3.v())) {
            const auto &[d_a03] =
                std::get<typename PatternImpossible::nested::Leaf>(_sv3.v());
            return ((d_a00 + d_a02) + d_a03);
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
