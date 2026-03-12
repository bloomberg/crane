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

unsigned int
PatternImpossible::complex_match(const PatternImpossible::three x) {
  return [&](void) {
    switch (x) {
    case three::One: {
      return 1u;
    }
    case three::Two: {
      return 2u;
    }
    case three::Three0: {
      return 3u;
    }
    }
  }();
}

unsigned int PatternImpossible::nested_match(
    const std::shared_ptr<PatternImpossible::nested> &n) {
  return std::visit(
      Overloaded{
          [](const typename PatternImpossible::nested::Leaf _args)
              -> unsigned int {
            unsigned int x = _args._a0;
            return std::move(x);
          },
          [](const typename PatternImpossible::nested::Node _args)
              -> unsigned int {
            std::shared_ptr<PatternImpossible::nested> n0 = _args._a0;
            std::shared_ptr<PatternImpossible::nested> n1 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename PatternImpossible::nested::Leaf _args)
                        -> unsigned int {
                      unsigned int a = _args._a0;
                      return std::visit(
                          Overloaded{
                              [&](const typename PatternImpossible::nested::Leaf
                                      _args) -> unsigned int {
                                unsigned int b = _args._a0;
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

unsigned int PatternImpossible::double_match(const PatternImpossible::three x,
                                             const PatternImpossible::three y) {
  return [&](void) {
    switch (x) {
    case three::One: {
      return [&](void) {
        switch (y) {
        case three::One: {
          return 1u;
        }
        case three::Two: {
          return 2u;
        }
        case three::Three0: {
          return 3u;
        }
        }
      }();
    }
    case three::Two: {
      return 10u;
    }
    case three::Three0: {
      return 20u;
    }
    }
  }();
}

unsigned int PatternImpossible::multi_arg_pattern(
    const std::shared_ptr<PatternImpossible::nested> &n) {
  return std::visit(
      Overloaded{
          [](const typename PatternImpossible::nested::Leaf _args)
              -> unsigned int { return 0u; },
          [](const typename PatternImpossible::nested::Node _args)
              -> unsigned int {
            std::shared_ptr<PatternImpossible::nested> n0 = _args._a0;
            std::shared_ptr<PatternImpossible::nested> n1 = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename PatternImpossible::nested::Leaf _args)
                        -> unsigned int {
                      unsigned int x = _args._a0;
                      return std::visit(
                          Overloaded{
                              [](const typename PatternImpossible::nested::Leaf
                                     _args) -> unsigned int { return 0u; },
                              [&](const typename PatternImpossible::nested::Node
                                      _args) -> unsigned int {
                                std::shared_ptr<PatternImpossible::nested> n2 =
                                    _args._a0;
                                std::shared_ptr<PatternImpossible::nested> n3 =
                                    _args._a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename PatternImpossible::
                                                nested::Leaf _args)
                                            -> unsigned int {
                                          unsigned int y = _args._a0;
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename PatternImpossible::
                                                          nested::Leaf _args)
                                                      -> unsigned int {
                                                    unsigned int z = _args._a0;
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
