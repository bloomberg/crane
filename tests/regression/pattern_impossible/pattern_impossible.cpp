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
    const auto &_m =
        *std::get_if<typename PatternImpossible::nested::Leaf>(&n->v());
    return _m.d_a0;
  } else {
    const auto &_m =
        *std::get_if<typename PatternImpossible::nested::Node>(&n->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            _sv0->v())) {
      const auto &_m0 =
          *std::get_if<typename PatternImpossible::nested::Leaf>(&_sv0->v());
      auto &&_sv1 = _m.d_a1;
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              _sv1->v())) {
        const auto &_m1 =
            *std::get_if<typename PatternImpossible::nested::Leaf>(&_sv1->v());
        return (_m0.d_a0 + _m1.d_a0);
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
    const auto &_m =
        *std::get_if<typename PatternImpossible::nested::Node>(&n->v());
    auto &&_sv0 = _m.d_a0;
    if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
            _sv0->v())) {
      const auto &_m0 =
          *std::get_if<typename PatternImpossible::nested::Leaf>(&_sv0->v());
      auto &&_sv1 = _m.d_a1;
      if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
              _sv1->v())) {
        return 0u;
      } else {
        const auto &_m1 =
            *std::get_if<typename PatternImpossible::nested::Node>(&_sv1->v());
        auto &&_sv2 = _m1.d_a0;
        if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                _sv2->v())) {
          const auto &_m2 =
              *std::get_if<typename PatternImpossible::nested::Leaf>(
                  &_sv2->v());
          auto &&_sv3 = _m1.d_a1;
          if (std::holds_alternative<typename PatternImpossible::nested::Leaf>(
                  _sv3->v())) {
            const auto &_m3 =
                *std::get_if<typename PatternImpossible::nested::Leaf>(
                    &_sv3->v());
            return ((_m0.d_a0 + _m2.d_a0) + _m3.d_a0);
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
