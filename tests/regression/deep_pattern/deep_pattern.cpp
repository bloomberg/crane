#include <deep_pattern.h>

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
DeepPattern::deep_match(const std::shared_ptr<DeepPattern::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename DeepPattern::tree::Node _args) -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args1)
                                  -> unsigned int {
                                return (_args0.d_a0 + _args1.d_a0);
                              },
                              [&](const typename DeepPattern::tree::Node _args1)
                                  -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args2) -> unsigned int {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args3)
                                                      -> unsigned int {
                                                    return ((_args0.d_a0 +
                                                             _args2.d_a0) +
                                                            _args3.d_a0);
                                                  },
                                                  [](const typename DeepPattern::
                                                         tree::Node _args3)
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
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args1)
                                  -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args2) -> unsigned int {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args3)
                                                      -> unsigned int {
                                                    return ((_args1.d_a0 +
                                                             _args2.d_a0) +
                                                            _args3.d_a0);
                                                  },
                                                  [&](const typename DeepPattern::
                                                          tree::Node _args3)
                                                      -> unsigned int {
                                                    return std::visit(
                                                        Overloaded{
                                                            [&](const typename DeepPattern::
                                                                    tree::Leaf
                                                                        _args4)
                                                                -> unsigned int {
                                                              return std::visit(
                                                                  Overloaded{
                                                                      [&](const typename DeepPattern::
                                                                              tree::Leaf
                                                                                  _args5)
                                                                          -> unsigned int {
                                                                        return (
                                                                            ((_args1
                                                                                  .d_a0 +
                                                                              _args2
                                                                                  .d_a0) +
                                                                             _args4
                                                                                 .d_a0) +
                                                                            _args5
                                                                                .d_a0);
                                                                      },
                                                                      [](const typename DeepPattern::
                                                                             tree::Node
                                                                                 _args5)
                                                                          -> unsigned int {
                                                                        return 0u;
                                                                      }},
                                                                  _args3.d_a1
                                                                      ->v());
                                                            },
                                                            [](const typename DeepPattern::
                                                                   tree::Node
                                                                       _args4)
                                                                -> unsigned int {
                                                              return 0u;
                                                            }},
                                                        _args3.d_a0->v());
                                                  }},
                                              _args.d_a1->v());
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args2) -> unsigned int {
                                          return 0u;
                                        }},
                                    _args0.d_a1->v());
                              },
                              [&](const typename DeepPattern::tree::Node _args1)
                                  -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args2) -> unsigned int {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args3)
                                                      -> unsigned int {
                                                    return std::visit(
                                                        Overloaded{
                                                            [&](const typename DeepPattern::
                                                                    tree::Leaf
                                                                        _args4)
                                                                -> unsigned int {
                                                              return std::visit(
                                                                  Overloaded{
                                                                      [&](const typename DeepPattern::
                                                                              tree::Leaf
                                                                                  _args5)
                                                                          -> unsigned int {
                                                                        return (
                                                                            ((_args2
                                                                                  .d_a0 +
                                                                              _args3
                                                                                  .d_a0) +
                                                                             _args4
                                                                                 .d_a0) +
                                                                            _args5
                                                                                .d_a0);
                                                                      },
                                                                      [](const typename DeepPattern::
                                                                             tree::Node
                                                                                 _args5)
                                                                          -> unsigned int {
                                                                        return 0u;
                                                                      }},
                                                                  _args.d_a1
                                                                      ->v());
                                                            },
                                                            [](const typename DeepPattern::
                                                                   tree::Node
                                                                       _args4)
                                                                -> unsigned int {
                                                              return 0u;
                                                            }},
                                                        _args0.d_a1->v());
                                                  },
                                                  [](const typename DeepPattern::
                                                         tree::Node _args3)
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
                          _args0.d_a0->v());
                    }},
                _args.d_a0->v());
          }},
      t->v());
}

__attribute__((pure)) unsigned int
DeepPattern::multi_constructor(const std::shared_ptr<DeepPattern::tree> &t1,
                               const std::shared_ptr<DeepPattern::tree> &t2) {
  return std::visit(
      Overloaded{
          [&](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args0)
                        -> unsigned int { return (_args.d_a0 + _args0.d_a0); },
                    [&](const typename DeepPattern::tree::Node _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args1)
                                  -> unsigned int {
                                return (_args.d_a0 + _args1.d_a0);
                              },
                              [](const typename DeepPattern::tree::Node _args1)
                                  -> unsigned int { return 0u; }},
                          _args0.d_a0->v());
                    }},
                t2->v());
          },
          [&](const typename DeepPattern::tree::Node _args) -> unsigned int {
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args0)
                        -> unsigned int {
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args1)
                                  -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args2) -> unsigned int {
                                          return (_args0.d_a0 + _args2.d_a0);
                                        },
                                        [&](const typename DeepPattern::tree::
                                                Node _args2) -> unsigned int {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args3)
                                                      -> unsigned int {
                                                    return std::visit(
                                                        Overloaded{
                                                            [&](const typename DeepPattern::
                                                                    tree::Leaf
                                                                        _args4)
                                                                -> unsigned int {
                                                              return (
                                                                  ((_args0
                                                                        .d_a0 +
                                                                    _args1
                                                                        .d_a0) +
                                                                   _args3
                                                                       .d_a0) +
                                                                  _args4.d_a0);
                                                            },
                                                            [](const typename DeepPattern::
                                                                   tree::Node
                                                                       _args4)
                                                                -> unsigned int {
                                                              return 0u;
                                                            }},
                                                        _args2.d_a1->v());
                                                  },
                                                  [](const typename DeepPattern::
                                                         tree::Node _args3)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              _args2.d_a0->v());
                                        }},
                                    t2->v());
                              },
                              [&](const typename DeepPattern::tree::Node _args1)
                                  -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args2) -> unsigned int {
                                          return (_args0.d_a0 + _args2.d_a0);
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args2) -> unsigned int {
                                          return 0u;
                                        }},
                                    t2->v());
                              }},
                          _args.d_a1->v());
                    },
                    [](const typename DeepPattern::tree::Node _args0)
                        -> unsigned int { return 0u; }},
                _args.d_a0->v());
          }},
      t1->v());
}

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

__attribute__((pure)) unsigned int DeepPattern::wildcard_with_bindings(
    const std::shared_ptr<DeepPattern::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename DeepPattern::tree::Node _args) -> unsigned int {
            unsigned int x = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args0)
                               -> unsigned int { return _args0.d_a0; },
                           [](const typename DeepPattern::tree::Node _args0)
                               -> unsigned int { return 0u; }},
                _args.d_a0->v());
            unsigned int y = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args1)
                               -> unsigned int { return _args1.d_a0; },
                           [](const typename DeepPattern::tree::Node _args1)
                               -> unsigned int { return 0u; }},
                _args.d_a1->v());
            return (std::move(x) + std::move(y));
          }},
      t->v());
}

std::shared_ptr<DeepPattern::tree>
DeepPattern::as_pattern_test(std::shared_ptr<DeepPattern::tree> t) {
  return std::visit(
      Overloaded{
          [&](const typename DeepPattern::tree::Leaf _args)
              -> std::shared_ptr<DeepPattern::tree> { return std::move(t); },
          [&](const typename DeepPattern::tree::Node _args)
              -> std::shared_ptr<DeepPattern::tree> { return std::move(t); }},
      t->v());
}

__attribute__((pure)) bool
DeepPattern::has_value(const std::shared_ptr<DeepPattern::tree> &t,
                       const unsigned int target) {
  return std::visit(
      Overloaded{[&](const typename DeepPattern::tree::Leaf _args) -> bool {
                   return _args.d_a0 == target;
                 },
                 [&](const typename DeepPattern::tree::Node _args) -> bool {
                   return (has_value(_args.d_a0, target) ||
                           has_value(_args.d_a1, target));
                 }},
      t->v());
}

__attribute__((pure)) unsigned int
DeepPattern::conditional_match(const std::shared_ptr<DeepPattern::tree> &t,
                               const unsigned int target) {
  return std::visit(
      Overloaded{
          [&](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            if (_args.d_a0 == target) {
              return 100u;
            } else {
              return _args.d_a0;
            }
          },
          [&](const typename DeepPattern::tree::Node _args) -> unsigned int {
            if (has_value(t, target)) {
              return 200u;
            } else {
              return std::visit(
                  Overloaded{[](const typename DeepPattern::tree::Leaf _args0)
                                 -> unsigned int { return _args0.d_a0; },
                             [](const typename DeepPattern::tree::Node _args0)
                                 -> unsigned int { return 0u; }},
                  _args.d_a0->v());
            }
          }},
      t->v());
}

__attribute__((pure)) unsigned int
DeepPattern::nested_let_match(const std::shared_ptr<DeepPattern::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            return _args.d_a0;
          },
          [](const typename DeepPattern::tree::Node _args) -> unsigned int {
            unsigned int a = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args0)
                               -> unsigned int { return _args0.d_a0; },
                           [](const typename DeepPattern::tree::Node _args0)
                               -> unsigned int { return 0u; }},
                _args.d_a0->v());
            unsigned int b = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args1)
                               -> unsigned int { return _args1.d_a0; },
                           [](const typename DeepPattern::tree::Node _args1)
                               -> unsigned int { return 0u; }},
                _args.d_a1->v());
            unsigned int c = (std::move(a) + std::move(b));
            unsigned int d = (std::move(c) * 2u);
            return (std::move(d) + 1u);
          }},
      t->v());
}
