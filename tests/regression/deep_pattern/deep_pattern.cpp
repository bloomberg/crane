#include <deep_pattern.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int DeepPattern::list_deep_match(
    const std::shared_ptr<DeepPattern::list<std::shared_ptr<DeepPattern::tree>>>
        &l) {
  return std::visit(
      Overloaded{
          [](const typename DeepPattern::list<
              std::shared_ptr<DeepPattern::tree>>::Nil _args) -> unsigned int {
            return 0u;
          },
          [](const typename DeepPattern::list<
              std::shared_ptr<DeepPattern::tree>>::Cons _args) -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::list<
                                  std::shared_ptr<DeepPattern::tree>>::Nil
                                      _args1) -> unsigned int {
                                return _args0.d_a0;
                              },
                              [&](const typename DeepPattern::list<
                                  std::shared_ptr<DeepPattern::tree>>::Cons
                                      _args1) -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args2) -> unsigned int {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          list<std::shared_ptr<
                                                              DeepPattern::
                                                                  tree>>::Nil
                                                              _args3)
                                                      -> unsigned int {
                                                    return (_args0.d_a0 +
                                                            _args2.d_a0);
                                                  },
                                                  [](const typename DeepPattern::
                                                         list<std::shared_ptr<
                                                             DeepPattern::
                                                                 tree>>::Cons
                                                             _args3)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              _args1.d_a1->v());
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args2) -> unsigned int {
                                          return 0u;
                                        }},
                                    _args1.d_a0->v());
                              }},
                          _args.d_a1->v());
                    },
                    [&](const typename DeepPattern::tree::Node _args0)
                        -> unsigned int {
                      return std::
                          visit(Overloaded{
                                    [&](const typename DeepPattern::tree::Leaf
                                            _args1) -> unsigned int {
                                      return std::
                                          visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args2)
                                                      -> unsigned int {
                                                    return std::
                                                        visit(Overloaded{
                                                                  [](const typename DeepPattern::list<
                                                                      std::shared_ptr<
                                                                          DeepPattern::
                                                                              tree>>::
                                                                         Nil _args3)
                                                                      -> unsigned int {
                                                                    return 0u;
                                                                  },
                                                                  [&](const typename DeepPattern::list<
                                                                      std::shared_ptr<
                                                                          DeepPattern::
                                                                              tree>>::
                                                                          Cons
                                                                              _args3)
                                                                      -> unsigned int {
                                                                    return std::visit(Overloaded{[&](const typename DeepPattern::
                                                                                                         tree::Leaf
                                                                                                             _args4) -> unsigned int {
                                                                                                   return std::visit(
                                                                                                       Overloaded{
                                                                                                           [&](const typename DeepPattern::list<
                                                                                                               std::shared_ptr<
                                                                                                                   DeepPattern::
                                                                                                                       tree>>::
                                                                                                                   Nil _args5)
                                                                                                               -> unsigned int {
                                                                                                             return (
                                                                                                                 (_args1
                                                                                                                      .d_a0 +
                                                                                                                  _args2
                                                                                                                      .d_a0) +
                                                                                                                 _args4
                                                                                                                     .d_a0);
                                                                                                           },
                                                                                                           [](const typename DeepPattern::list<
                                                                                                               std::shared_ptr<
                                                                                                                   DeepPattern::
                                                                                                                       tree>>::
                                                                                                                  Cons
                                                                                                                      _args5)
                                                                                                               -> unsigned int {
                                                                                                             return 0u;
                                                                                                           }},
                                                                                                       _args3
                                                                                                           .d_a1
                                                                                                           ->v());
                                                                                                 },
                                                                                                 [&](const typename DeepPattern::
                                                                                                         tree::Node
                                                                                                             _args4) -> unsigned int {
                                                                                                   return std::visit(
                                                                                                       Overloaded{
                                                                                                           [&](const typename DeepPattern::
                                                                                                                   tree::Leaf
                                                                                                                       _args5)
                                                                                                               -> unsigned int {
                                                                                                             return std::visit(
                                                                                                                 Overloaded{[&](const typename DeepPattern::tree::Leaf
                                                                                                                                    _args6) -> unsigned int {
                                                                                                                              return std::
                                                                                                                                  visit(
                                                                                                                                      Overloaded{
                                                                                                                                          [&](const typename DeepPattern::
                                                                                                                                                  list<
                                                                                                                                                      std::
                                                                                                                                                          shared_ptr<
                                                                                                                                                              DeepPattern::
                                                                                                                                                                  tree>>::Nil _args7) -> unsigned int {
                                                                                                                                            return (
                                                                                                                                                ((_args1
                                                                                                                                                      .d_a0 +
                                                                                                                                                  _args2
                                                                                                                                                      .d_a0) +
                                                                                                                                                 _args5
                                                                                                                                                     .d_a0) +
                                                                                                                                                _args6
                                                                                                                                                    .d_a0);
                                                                                                                                          },
                                                                                                                                          [](const typename DeepPattern::list<
                                                                                                                                              std::shared_ptr<
                                                                                                                                                  DeepPattern::
                                                                                                                                                      tree>>::
                                                                                                                                                 Cons
                                                                                                                                                     _args7)
                                                                                                                                              -> unsigned int {
                                                                                                                                            return 0u;
                                                                                                                                          }},
                                                                                                                                      _args3
                                                                                                                                          .d_a1
                                                                                                                                          ->v());
                                                                                                                            },
                                                                                                                            [](const typename DeepPattern::
                                                                                                                                   tree::Node
                                                                                                                                       _args6)
                                                                                                                                -> unsigned int {
                                                                                                                              return 0u;
                                                                                                                            }},
                                                                                                                 _args4
                                                                                                                     .d_a1
                                                                                                                     ->v());
                                                                                                           },
                                                                                                           [](const typename DeepPattern::
                                                                                                                  tree::Node
                                                                                                                      _args5)
                                                                                                               -> unsigned int {
                                                                                                             return 0u;
                                                                                                           }},
                                                                                                       _args4
                                                                                                           .d_a0
                                                                                                           ->v());
                                                                                                 }},
                                                                                      _args3
                                                                                          .d_a0
                                                                                          ->v());
                                                                  }},
                                                              _args.d_a1->v());
                                                  },
                                                  [](const typename DeepPattern::
                                                         tree::Node _args2)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              _args0.d_a1->v());
                                    },
                                    [](const typename DeepPattern::tree::Node
                                           _args1) -> unsigned int {
                                      return 0u;
                                    }},
                                _args0.d_a0->v());
                    }},
                _args.d_a0->v());
          }},
      l->v());
}

std::shared_ptr<DeepPattern::tree>
DeepPattern::as_pattern_test(std::shared_ptr<DeepPattern::tree> t) {
  return std::move(t);
}
