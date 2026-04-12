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
  return std::visit(
      Overloaded{
          [](const typename PatternImpossible::nested::Leaf &_args)
              -> unsigned int { return _args.d_a0; },
          [](const typename PatternImpossible::nested::Node &_args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename PatternImpossible::nested::Leaf &_args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename PatternImpossible::nested::Leaf
                                      &_args1) -> unsigned int {
                                return (_args0.d_a0 + _args1.d_a0);
                              },
                              [](const typename PatternImpossible::nested::Node
                                     &) -> unsigned int { return 0u; }},
                          _args.d_a1->v());
                    },
                    [](const typename PatternImpossible::nested::Node &)
                        -> unsigned int { return 0u; }},
                _args.d_a0->v());
          }},
      n->v());
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
  return std::visit(
      Overloaded{
          [](const typename PatternImpossible::nested::Leaf &) -> unsigned int {
            return 0u;
          },
          [](const typename PatternImpossible::nested::Node &_args)
              -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename PatternImpossible::nested::Leaf &_args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [](const typename PatternImpossible::nested::Leaf
                                     &) -> unsigned int { return 0u; },
                              [&](const typename PatternImpossible::nested::Node
                                      &_args1) -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename PatternImpossible::
                                                nested::Leaf &_args2)
                                            -> unsigned int {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename PatternImpossible::
                                                          nested::Leaf &_args3)
                                                      -> unsigned int {
                                                    return ((_args0.d_a0 +
                                                             _args2.d_a0) +
                                                            _args3.d_a0);
                                                  },
                                                  [](const typename PatternImpossible::
                                                         nested::Node &)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              _args1.d_a1->v());
                                        },
                                        [](const typename PatternImpossible::
                                               nested::Node &) -> unsigned int {
                                          return 0u;
                                        }},
                                    _args1.d_a0->v());
                              }},
                          _args.d_a1->v());
                    },
                    [](const typename PatternImpossible::nested::Node &)
                        -> unsigned int { return 0u; }},
                _args.d_a0->v());
          }},
      n->v());
}
