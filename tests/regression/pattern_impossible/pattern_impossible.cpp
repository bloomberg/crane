#include <pattern_impossible.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
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

__attribute__((pure)) unsigned int PatternImpossible::nested_match(
    const std::shared_ptr<PatternImpossible::nested> &n) {
  if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
          n->v())) {
    const auto &[d_a0] =
        std::get<typename PatternImpossible::nested::Leaf>(n->v());
    return d_a0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename PatternImpossible::nested::Node>(n->v());
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            d_a0->v())) {
      const auto &[d_a00] =
          std::get<typename PatternImpossible::nested::Leaf>(d_a0->v());
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              d_a1->v())) {
        const auto &[d_a01] =
            std::get<typename PatternImpossible::nested::Leaf>(d_a1->v());
        return (d_a00 + d_a01);
      } else {
        return 0u;
      }
    } else {
      return 0u;
    }
  }
}

__attribute__((pure)) unsigned int
PatternImpossible::double_match(const PatternImpossible::Three x,
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

__attribute__((pure)) unsigned int PatternImpossible::multi_arg_pattern(
    const std::shared_ptr<PatternImpossible::nested> &n) {
  if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
          n->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename PatternImpossible::nested::Node>(n->v());
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            d_a0->v())) {
      const auto &[d_a00] =
          std::get<typename PatternImpossible::nested::Leaf>(d_a0->v());
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              d_a1->v())) {
        return 0u;
      } else {
        const auto &[d_a01, d_a11] =
            std::get<typename PatternImpossible::nested::Node>(d_a1->v());
        if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                d_a01->v())) {
          const auto &[d_a02] =
              std::get<typename PatternImpossible::nested::Leaf>(d_a01->v());
          if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                  d_a11->v())) {
            const auto &[d_a03] =
                std::get<typename PatternImpossible::nested::Leaf>(d_a11->v());
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
