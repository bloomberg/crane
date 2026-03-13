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
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename DeepPattern::tree::Node _args) -> unsigned int {
            std::shared_ptr<DeepPattern::tree> t0 = _args.d_a0;
            std::shared_ptr<DeepPattern::tree> t1 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args)
                        -> unsigned int {
                      unsigned int a = _args.d_a0;
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args)
                                  -> unsigned int {
                                unsigned int b = _args.d_a0;
                                return (std::move(a) + std::move(b));
                              },
                              [&](const typename DeepPattern::tree::Node _args)
                                  -> unsigned int {
                                std::shared_ptr<DeepPattern::tree> t2 =
                                    _args.d_a0;
                                std::shared_ptr<DeepPattern::tree> t3 =
                                    _args.d_a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args) -> unsigned int {
                                          unsigned int b = _args.d_a0;
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args)
                                                      -> unsigned int {
                                                    unsigned int c = _args.d_a0;
                                                    return ((std::move(a) +
                                                             std::move(b)) +
                                                            std::move(c));
                                                  },
                                                  [](const typename DeepPattern::
                                                         tree::Node _args)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              std::move(t3)->v());
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args) -> unsigned int {
                                          return 0u;
                                        }},
                                    std::move(t2)->v());
                              }},
                          std::move(t1)->v());
                    },
                    [&](const typename DeepPattern::tree::Node _args)
                        -> unsigned int {
                      std::shared_ptr<DeepPattern::tree> t2 = _args.d_a0;
                      std::shared_ptr<DeepPattern::tree> t3 = _args.d_a1;
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args)
                                  -> unsigned int {
                                unsigned int a = _args.d_a0;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args) -> unsigned int {
                                          unsigned int b = _args.d_a0;
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args)
                                                      -> unsigned int {
                                                    unsigned int c = _args.d_a0;
                                                    return ((std::move(a) +
                                                             std::move(b)) +
                                                            std::move(c));
                                                  },
                                                  [&](const typename DeepPattern::
                                                          tree::Node _args)
                                                      -> unsigned int {
                                                    std::shared_ptr<
                                                        DeepPattern::tree>
                                                        t4 = _args.d_a0;
                                                    std::shared_ptr<
                                                        DeepPattern::tree>
                                                        t5 = _args.d_a1;
                                                    return std::visit(
                                                        Overloaded{
                                                            [&](const typename DeepPattern::
                                                                    tree::Leaf
                                                                        _args)
                                                                -> unsigned int {
                                                              unsigned int c =
                                                                  _args.d_a0;
                                                              return std::visit(
                                                                  Overloaded{
                                                                      [&](const typename DeepPattern::
                                                                              tree::Leaf
                                                                                  _args)
                                                                          -> unsigned int {
                                                                        unsigned int d =
                                                                            _args
                                                                                .d_a0;
                                                                        return (
                                                                            ((std::move(
                                                                                  a) +
                                                                              std::move(
                                                                                  b)) +
                                                                             std::move(
                                                                                 c)) +
                                                                            std::move(
                                                                                d));
                                                                      },
                                                                      [](const typename DeepPattern::
                                                                             tree::Node
                                                                                 _args)
                                                                          -> unsigned int {
                                                                        return 0u;
                                                                      }},
                                                                  std::move(t5)
                                                                      ->v());
                                                            },
                                                            [](const typename DeepPattern::
                                                                   tree::Node
                                                                       _args)
                                                                -> unsigned int {
                                                              return 0u;
                                                            }},
                                                        std::move(t4)->v());
                                                  }},
                                              std::move(t1)->v());
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args) -> unsigned int {
                                          return 0u;
                                        }},
                                    std::move(t3)->v());
                              },
                              [&](const typename DeepPattern::tree::Node _args)
                                  -> unsigned int {
                                std::shared_ptr<DeepPattern::tree> t4 =
                                    _args.d_a0;
                                std::shared_ptr<DeepPattern::tree> t5 =
                                    _args.d_a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args) -> unsigned int {
                                          unsigned int a = _args.d_a0;
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args)
                                                      -> unsigned int {
                                                    unsigned int b = _args.d_a0;
                                                    return std::visit(
                                                        Overloaded{
                                                            [&](const typename DeepPattern::
                                                                    tree::Leaf
                                                                        _args)
                                                                -> unsigned int {
                                                              unsigned int c =
                                                                  _args.d_a0;
                                                              return std::visit(
                                                                  Overloaded{
                                                                      [&](const typename DeepPattern::
                                                                              tree::Leaf
                                                                                  _args)
                                                                          -> unsigned int {
                                                                        unsigned int d =
                                                                            _args
                                                                                .d_a0;
                                                                        return (
                                                                            ((std::move(
                                                                                  a) +
                                                                              std::move(
                                                                                  b)) +
                                                                             std::move(
                                                                                 c)) +
                                                                            std::move(
                                                                                d));
                                                                      },
                                                                      [](const typename DeepPattern::
                                                                             tree::Node
                                                                                 _args)
                                                                          -> unsigned int {
                                                                        return 0u;
                                                                      }},
                                                                  std::move(t1)
                                                                      ->v());
                                                            },
                                                            [](const typename DeepPattern::
                                                                   tree::Node
                                                                       _args)
                                                                -> unsigned int {
                                                              return 0u;
                                                            }},
                                                        std::move(t3)->v());
                                                  },
                                                  [](const typename DeepPattern::
                                                         tree::Node _args)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              std::move(t5)->v());
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args) -> unsigned int {
                                          return 0u;
                                        }},
                                    std::move(t4)->v());
                              }},
                          std::move(t2)->v());
                    }},
                std::move(t0)->v());
          }},
      t->v());
}

__attribute__((pure)) unsigned int
DeepPattern::multi_constructor(const std::shared_ptr<DeepPattern::tree> &t1,
                               const std::shared_ptr<DeepPattern::tree> &t2) {
  return std::visit(
      Overloaded{
          [&](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            unsigned int a = _args.d_a0;
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args)
                        -> unsigned int {
                      unsigned int b = _args.d_a0;
                      return (std::move(a) + std::move(b));
                    },
                    [&](const typename DeepPattern::tree::Node _args)
                        -> unsigned int {
                      std::shared_ptr<DeepPattern::tree> t = _args.d_a0;
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args)
                                  -> unsigned int {
                                unsigned int b = _args.d_a0;
                                return (std::move(a) + std::move(b));
                              },
                              [](const typename DeepPattern::tree::Node _args)
                                  -> unsigned int { return 0u; }},
                          std::move(t)->v());
                    }},
                t2->v());
          },
          [&](const typename DeepPattern::tree::Node _args) -> unsigned int {
            std::shared_ptr<DeepPattern::tree> t = _args.d_a0;
            std::shared_ptr<DeepPattern::tree> t0 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args)
                        -> unsigned int {
                      unsigned int a = _args.d_a0;
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args)
                                  -> unsigned int {
                                unsigned int b = _args.d_a0;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args) -> unsigned int {
                                          unsigned int b0 = _args.d_a0;
                                          return (std::move(a) + std::move(b0));
                                        },
                                        [&](const typename DeepPattern::tree::
                                                Node _args) -> unsigned int {
                                          std::shared_ptr<DeepPattern::tree>
                                              t3 = _args.d_a0;
                                          std::shared_ptr<DeepPattern::tree>
                                              t4 = _args.d_a1;
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          tree::Leaf _args)
                                                      -> unsigned int {
                                                    unsigned int c = _args.d_a0;
                                                    return std::visit(
                                                        Overloaded{
                                                            [&](const typename DeepPattern::
                                                                    tree::Leaf
                                                                        _args)
                                                                -> unsigned int {
                                                              unsigned int d =
                                                                  _args.d_a0;
                                                              return (
                                                                  ((std::move(
                                                                        a) +
                                                                    std::move(
                                                                        b)) +
                                                                   std::move(
                                                                       c)) +
                                                                  std::move(d));
                                                            },
                                                            [](const typename DeepPattern::
                                                                   tree::Node
                                                                       _args)
                                                                -> unsigned int {
                                                              return 0u;
                                                            }},
                                                        std::move(t4)->v());
                                                  },
                                                  [](const typename DeepPattern::
                                                         tree::Node _args)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              std::move(t3)->v());
                                        }},
                                    t2->v());
                              },
                              [&](const typename DeepPattern::tree::Node _args)
                                  -> unsigned int {
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args) -> unsigned int {
                                          unsigned int b = _args.d_a0;
                                          return (std::move(a) + std::move(b));
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args) -> unsigned int {
                                          return 0u;
                                        }},
                                    t2->v());
                              }},
                          std::move(t0)->v());
                    },
                    [](const typename DeepPattern::tree::Node _args)
                        -> unsigned int { return 0u; }},
                std::move(t)->v());
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
            std::shared_ptr<DeepPattern::tree> t = _args.d_a0;
            std::shared_ptr<
                DeepPattern::list<std::shared_ptr<DeepPattern::tree>>>
                l0 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename DeepPattern::tree::Leaf _args)
                        -> unsigned int {
                      unsigned int a = _args.d_a0;
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::list<
                                  std::shared_ptr<DeepPattern::tree>>::Nil
                                      _args) -> unsigned int {
                                return std::move(a);
                              },
                              [&](const typename DeepPattern::list<
                                  std::shared_ptr<DeepPattern::tree>>::Cons
                                      _args) -> unsigned int {
                                std::shared_ptr<DeepPattern::tree> t0 =
                                    _args.d_a0;
                                std::shared_ptr<DeepPattern::list<
                                    std::shared_ptr<DeepPattern::tree>>>
                                    l1 = _args.d_a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename DeepPattern::tree::
                                                Leaf _args) -> unsigned int {
                                          unsigned int b = _args.d_a0;
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename DeepPattern::
                                                          list<std::shared_ptr<
                                                              DeepPattern::
                                                                  tree>>::Nil
                                                              _args)
                                                      -> unsigned int {
                                                    return (std::move(a) +
                                                            std::move(b));
                                                  },
                                                  [](const typename DeepPattern::
                                                         list<std::shared_ptr<
                                                             DeepPattern::
                                                                 tree>>::Cons
                                                             _args)
                                                      -> unsigned int {
                                                    return 0u;
                                                  }},
                                              std::move(l1)->v());
                                        },
                                        [](const typename DeepPattern::tree::
                                               Node _args) -> unsigned int {
                                          return 0u;
                                        }},
                                    std::move(t0)->v());
                              }},
                          std::move(l0)->v());
                    },
                    [&](const typename DeepPattern::tree::Node _args)
                        -> unsigned int {
                      std::shared_ptr<DeepPattern::tree> t0 = _args.d_a0;
                      std::shared_ptr<DeepPattern::tree> t1 = _args.d_a1;
                      return std::visit(
                          Overloaded{
                              [&](const typename DeepPattern::tree::Leaf _args)
                                  -> unsigned int {
                                unsigned int a = _args.d_a0;
                                return std::visit(
                                    Overloaded{[&](const typename DeepPattern::
                                                       tree::Leaf _args)
                                                   -> unsigned int {
                                                 unsigned int b = _args.d_a0;
                                                 return std::visit(Overloaded{[](const typename DeepPattern::list<
                                                                                  std::shared_ptr<
                                                                                      DeepPattern::
                                                                                          tree>>::
                                                                                     Nil _args)
                                                                                  -> unsigned int {
                                                                                return 0u;
                                                                              },
                                                                              [&](const typename DeepPattern::list<
                                                                                  std::shared_ptr<
                                                                                      DeepPattern::
                                                                                          tree>>::Cons _args) -> unsigned int {
                                                                                std::shared_ptr<
                                                                                    DeepPattern::
                                                                                        tree>
                                                                                    t2 =
                                                                                        _args
                                                                                            .d_a0;
                                                                                std::shared_ptr<
                                                                                    DeepPattern::list<
                                                                                        std::shared_ptr<
                                                                                            DeepPattern::
                                                                                                tree>>>
                                                                                    l1 =
                                                                                        _args
                                                                                            .d_a1;
                                                                                return std::
                                                                                    visit(
                                                                                        Overloaded{
                                                                                            [&](const typename DeepPattern::
                                                                                                    tree::Leaf
                                                                                                        _args)
                                                                                                -> unsigned int {
                                                                                              unsigned int
                                                                                                  c = _args
                                                                                                          .d_a0;
                                                                                              return std::visit(
                                                                                                  Overloaded{
                                                                                                      [&](const typename DeepPattern::list<
                                                                                                          std::shared_ptr<
                                                                                                              DeepPattern::
                                                                                                                  tree>>::
                                                                                                              Nil _args)
                                                                                                          -> unsigned int {
                                                                                                        return (
                                                                                                            (std::move(
                                                                                                                 a) +
                                                                                                             std::move(
                                                                                                                 b)) +
                                                                                                            std::move(
                                                                                                                c));
                                                                                                      },
                                                                                                      [](const typename DeepPattern::list<
                                                                                                          std::shared_ptr<
                                                                                                              DeepPattern::
                                                                                                                  tree>>::
                                                                                                             Cons
                                                                                                                 _args)
                                                                                                          -> unsigned int {
                                                                                                        return 0u;
                                                                                                      }},
                                                                                                  std::move(
                                                                                                      l1)
                                                                                                      ->v());
                                                                                            },
                                                                                            [&](const typename DeepPattern::
                                                                                                    tree::Node
                                                                                                        _args)
                                                                                                -> unsigned int {
                                                                                              std::shared_ptr<
                                                                                                  DeepPattern::
                                                                                                      tree>
                                                                                                  t3 =
                                                                                                      _args
                                                                                                          .d_a0;
                                                                                              std::shared_ptr<
                                                                                                  DeepPattern::
                                                                                                      tree>
                                                                                                  t4 =
                                                                                                      _args
                                                                                                          .d_a1;
                                                                                              return std::
                                                                                                  visit(Overloaded{[&](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
                                                                                                                     unsigned int
                                                                                                                         c = _args
                                                                                                                                 .d_a0;
                                                                                                                     return std::visit(
                                                                                                                         Overloaded{
                                                                                                                             [&](const typename DeepPattern::
                                                                                                                                     tree::Leaf
                                                                                                                                         _args)
                                                                                                                                 -> unsigned int {
                                                                                                                               unsigned int
                                                                                                                                   d = _args
                                                                                                                                           .d_a0;
                                                                                                                               return std::visit(
                                                                                                                                   Overloaded{
                                                                                                                                       [&](const typename DeepPattern::list<
                                                                                                                                           std::shared_ptr<
                                                                                                                                               DeepPattern::
                                                                                                                                                   tree>>::
                                                                                                                                               Nil _args)
                                                                                                                                           -> unsigned int {
                                                                                                                                         return (
                                                                                                                                             ((std::move(
                                                                                                                                                   a) +
                                                                                                                                               std::move(
                                                                                                                                                   b)) +
                                                                                                                                              std::move(
                                                                                                                                                  c)) +
                                                                                                                                             std::move(
                                                                                                                                                 d));
                                                                                                                                       },
                                                                                                                                       [](const typename DeepPattern::list<
                                                                                                                                           std::shared_ptr<
                                                                                                                                               DeepPattern::
                                                                                                                                                   tree>>::
                                                                                                                                              Cons
                                                                                                                                                  _args)
                                                                                                                                           -> unsigned int {
                                                                                                                                         return 0u;
                                                                                                                                       }},
                                                                                                                                   std::move(
                                                                                                                                       l1)
                                                                                                                                       ->v());
                                                                                                                             },
                                                                                                                             [](const typename DeepPattern::
                                                                                                                                    tree::Node
                                                                                                                                        _args)
                                                                                                                                 -> unsigned int {
                                                                                                                               return 0u;
                                                                                                                             }},
                                                                                                                         std::move(
                                                                                                                             t4)
                                                                                                                             ->v());
                                                                                                                   },
                                                                                                                   [](const typename DeepPattern::
                                                                                                                          tree::Node
                                                                                                                              _args)
                                                                                                                       -> unsigned int {
                                                                                                                     return 0u;
                                                                                                                   }},
                                                                                                        std::move(
                                                                                                            t3)
                                                                                                            ->v());
                                                                                            }},
                                                                                        std::move(
                                                                                            t2)
                                                                                            ->v());
                                                                              }},
                                                                   std::move(l0)
                                                                       ->v());
                                               },
                                               [](const typename DeepPattern::
                                                      tree::Node _args)
                                                   -> unsigned int {
                                                 return 0u;
                                               }},
                                    std::move(t1)->v());
                              },
                              [](const typename DeepPattern::tree::Node _args)
                                  -> unsigned int { return 0u; }},
                          std::move(t0)->v());
                    }},
                std::move(t)->v());
          }},
      l->v());
}

__attribute__((pure)) unsigned int DeepPattern::wildcard_with_bindings(
    const std::shared_ptr<DeepPattern::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename DeepPattern::tree::Node _args) -> unsigned int {
            std::shared_ptr<DeepPattern::tree> l = _args.d_a0;
            std::shared_ptr<DeepPattern::tree> r = _args.d_a1;
            unsigned int x = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args)
                               -> unsigned int {
                             unsigned int a = _args.d_a0;
                             return std::move(a);
                           },
                           [](const typename DeepPattern::tree::Node _args)
                               -> unsigned int { return 0u; }},
                std::move(l)->v());
            unsigned int y = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args)
                               -> unsigned int {
                             unsigned int b = _args.d_a0;
                             return std::move(b);
                           },
                           [](const typename DeepPattern::tree::Node _args)
                               -> unsigned int { return 0u; }},
                std::move(r)->v());
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
                   unsigned int n = _args.d_a0;
                   return std::move(n) == target;
                 },
                 [&](const typename DeepPattern::tree::Node _args) -> bool {
                   std::shared_ptr<DeepPattern::tree> l = _args.d_a0;
                   std::shared_ptr<DeepPattern::tree> r = _args.d_a1;
                   return (has_value(std::move(l), target) ||
                           has_value(std::move(r), target));
                 }},
      t->v());
}

__attribute__((pure)) unsigned int
DeepPattern::conditional_match(const std::shared_ptr<DeepPattern::tree> &t,
                               const unsigned int target) {
  return std::visit(
      Overloaded{
          [&](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            if (n == target) {
              return 100u;
            } else {
              return std::move(n);
            }
          },
          [&](const typename DeepPattern::tree::Node _args) -> unsigned int {
            std::shared_ptr<DeepPattern::tree> l = _args.d_a0;
            if (has_value(t, target)) {
              return 200u;
            } else {
              return std::visit(
                  Overloaded{[](const typename DeepPattern::tree::Leaf _args)
                                 -> unsigned int {
                               unsigned int a = _args.d_a0;
                               return std::move(a);
                             },
                             [](const typename DeepPattern::tree::Node _args)
                                 -> unsigned int { return 0u; }},
                  std::move(l)->v());
            }
          }},
      t->v());
}

__attribute__((pure)) unsigned int
DeepPattern::nested_let_match(const std::shared_ptr<DeepPattern::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename DeepPattern::tree::Leaf _args) -> unsigned int {
            unsigned int n = _args.d_a0;
            return std::move(n);
          },
          [](const typename DeepPattern::tree::Node _args) -> unsigned int {
            std::shared_ptr<DeepPattern::tree> l = _args.d_a0;
            std::shared_ptr<DeepPattern::tree> r = _args.d_a1;
            unsigned int a = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args)
                               -> unsigned int {
                             unsigned int x = _args.d_a0;
                             return std::move(x);
                           },
                           [](const typename DeepPattern::tree::Node _args)
                               -> unsigned int { return 0u; }},
                std::move(l)->v());
            unsigned int b = std::visit(
                Overloaded{[](const typename DeepPattern::tree::Leaf _args)
                               -> unsigned int {
                             unsigned int y = _args.d_a0;
                             return std::move(y);
                           },
                           [](const typename DeepPattern::tree::Node _args)
                               -> unsigned int { return 0u; }},
                std::move(r)->v());
            unsigned int c = (std::move(a) + std::move(b));
            unsigned int d = (std::move(c) * 2u);
            return (std::move(d) + 1u);
          }},
      t->v());
}
