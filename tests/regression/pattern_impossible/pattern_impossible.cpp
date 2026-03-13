#include <pattern_impossible.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
PatternImpossible::complex_match(const PatternImpossible::Three x) {
  return [&](void) {
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
    }
  }();
}

__attribute__((pure)) unsigned int PatternImpossible::nested_match(
    const std::shared_ptr<PatternImpossible::nested> &n) {
  return std::visit(
      Overloaded{
          [](const typename PatternImpossible::nested::Leaf _args)
              -> unsigned int {
            unsigned int x = _args.d_a0;
            return std::move(x);
          },
          [](const typename PatternImpossible::nested::Node _args)
              -> unsigned int {
            std::shared_ptr<PatternImpossible::nested> n0 = _args.d_a0;
            std::shared_ptr<PatternImpossible::nested> n1 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename PatternImpossible::nested::Leaf _args)
                        -> unsigned int {
                      unsigned int a = _args.d_a0;
                      return std::visit(
                          Overloaded{
                              [&](const typename PatternImpossible::nested::Leaf
                                      _args) -> unsigned int {
                                unsigned int b = _args.d_a0;
                                return (std::move(a) + std::move(b));
                              },
                              [](const typename PatternImpossible::nested::Node
                                     _args) -> unsigned int { return 0u; }},
                          std::move(n1)->v());
                    },
                    [](const typename PatternImpossible::nested::Node _args)
                        -> unsigned int { return 0u; }},
                std::move(n0)->v());
          }},
      n->v());
}

__attribute__((pure)) unsigned int
PatternImpossible::double_match(const PatternImpossible::Three x,
                                const PatternImpossible::Three y) {
  return [&](void) {
    switch (x) {
    case Three::e_ONE: {
      return [&](void) {
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
        }
      }();
    }
    case Three::e_TWO: {
      return 10u;
    }
    case Three::e_THREE0: {
      return 20u;
    }
    }
  }();
}

__attribute__((pure)) unsigned int PatternImpossible::multi_arg_pattern(
    const std::shared_ptr<PatternImpossible::nested> &n) {
  return std::visit(
      Overloaded{
          [](const typename PatternImpossible::nested::Leaf _args)
              -> unsigned int { return 0u; },
          [](const typename PatternImpossible::nested::Node _args)
              -> unsigned int {
            std::shared_ptr<PatternImpossible::nested> n0 = _args.d_a0;
            std::shared_ptr<PatternImpossible::nested> n1 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename PatternImpossible::nested::Leaf _args)
                        -> unsigned int {
                      unsigned int x = _args.d_a0;
                      return std::visit(
                          Overloaded{
                              [](const typename PatternImpossible::nested::Leaf
                                     _args) -> unsigned int { return 0u; },
                              [&](const typename PatternImpossible::nested::Node
                                      _args) -> unsigned int {
                                std::shared_ptr<PatternImpossible::nested> n2 =
                                    _args.d_a0;
                                std::shared_ptr<PatternImpossible::nested> n3 =
                                    _args.d_a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename PatternImpossible::
                                                nested::Leaf _args)
                                            -> unsigned int {
                                          unsigned int y = _args.d_a0;
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename PatternImpossible::
                                                          nested::Leaf _args)
                                                      -> unsigned int {
                                                    unsigned int z = _args.d_a0;
                                                    return ((std::move(x) +
                                                             std::move(y)) +
                                                            std::move(z));
                                                  },
                                                  [](const typename PatternImpossible::
                                                         nested::Node _args)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              std::move(n3)->v());
                                        },
                                        [](const typename PatternImpossible::
                                               nested::Node _args)
                                            -> unsigned int { return 0u; }},
                                    std::move(n2)->v());
                              }},
                          std::move(n1)->v());
                    },
                    [](const typename PatternImpossible::nested::Node _args)
                        -> unsigned int { return 0u; }},
                std::move(n0)->v());
          }},
      n->v());
}
