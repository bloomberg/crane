#include <binomial_heap.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<BinomialHeap::tree>
BinomialHeap::smash(const std::shared_ptr<BinomialHeap::tree> &t,
                    const std::shared_ptr<BinomialHeap::tree> &u) {
  return std::visit(
      Overloaded{
          [&](const typename BinomialHeap::tree::Node &_args)
              -> std::shared_ptr<BinomialHeap::tree> {
            return std::visit(
                Overloaded{
                    [](const typename BinomialHeap::tree::Node &)
                        -> std::shared_ptr<BinomialHeap::tree> {
                      return tree::leaf();
                    },
                    [&](const typename BinomialHeap::tree::Leaf &)
                        -> std::shared_ptr<BinomialHeap::tree> {
                      return std::visit(
                          Overloaded{
                              [&](const typename BinomialHeap::tree::Node
                                      &_args1)
                                  -> std::shared_ptr<BinomialHeap::tree> {
                                return std::visit(
                                    Overloaded{[](const typename BinomialHeap::
                                                      tree::Node &)
                                                   -> std::shared_ptr<
                                                       BinomialHeap::tree> {
                                                 return tree::leaf();
                                               },
                                               [&](const typename BinomialHeap::
                                                       tree::Leaf &)
                                                   -> std::shared_ptr<
                                                       BinomialHeap::tree> {
                                                 if (_args1.d_a0 < _args.d_a0) {
                                                   return tree::node(
                                                       _args.d_a0,
                                                       tree::node(_args1.d_a0,
                                                                  _args1.d_a1,
                                                                  _args.d_a1),
                                                       tree::leaf());
                                                 } else {
                                                   return tree::node(
                                                       _args1.d_a0,
                                                       tree::node(_args.d_a0,
                                                                  _args.d_a1,
                                                                  _args1.d_a1),
                                                       tree::leaf());
                                                 }
                                               }},
                                    _args1.d_a2->v());
                              },
                              [](const typename BinomialHeap::tree::Leaf &)
                                  -> std::shared_ptr<BinomialHeap::tree> {
                                return tree::leaf();
                              }},
                          u->v());
                    }},
                _args.d_a2->v());
          },
          [](const typename BinomialHeap::tree::Leaf &)
              -> std::shared_ptr<BinomialHeap::tree> { return tree::leaf(); }},
      t->v());
}

std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> BinomialHeap::carry(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q,
    std::shared_ptr<BinomialHeap::tree> t) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil &)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return std::visit(
                Overloaded{
                    [&](const typename BinomialHeap::tree::Node &)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<std::shared_ptr<BinomialHeap::tree>>::cons(
                          t, List<std::shared_ptr<BinomialHeap::tree>>::nil());
                    },
                    [](const typename BinomialHeap::tree::Leaf &)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<std::shared_ptr<BinomialHeap::tree>>::nil();
                    }},
                t->v());
          },
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                  &_args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return std::visit(
                Overloaded{
                    [&](const typename BinomialHeap::tree::Node &)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return std::visit(
                          Overloaded{
                              [&](const typename BinomialHeap::tree::Node &)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                return List<
                                    std::shared_ptr<BinomialHeap::tree>>::
                                    cons(tree::leaf(),
                                         carry(_args.d_a1,
                                               smash(t, _args.d_a0)));
                              },
                              [&](const typename BinomialHeap::tree::Leaf &)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                return List<std::shared_ptr<
                                    BinomialHeap::tree>>::cons(_args.d_a0,
                                                               _args.d_a1);
                              }},
                          t->v());
                    },
                    [&](const typename BinomialHeap::tree::Leaf &)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<std::shared_ptr<BinomialHeap::tree>>::cons(
                          t, _args.d_a1);
                    }},
                _args.d_a0->v());
          }},
      q->v());
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::insert(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return carry(q, tree::node(x, tree::leaf(), tree::leaf()));
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::join(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q,
    std::shared_ptr<BinomialHeap::tree> c) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil &)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return carry(q, std::move(c));
          },
          [&](const typename List<std::shared_ptr<
                  BinomialHeap::tree>>::Cons &_args) -> std::
                                                         shared_ptr<List<
                                                             std::shared_ptr<
                                                                 BinomialHeap::
                                                                     tree>>> {
                                                           return std::
                                                               visit(Overloaded{
                                                                         [&](const typename BinomialHeap::tree::Node
                                                                                 &) -> std::
                                                                                        shared_ptr<List<
                                                                                            std::shared_ptr<
                                                                                                BinomialHeap::
                                                                                                    tree>>> {
                                                                                          return std::visit(
                                                                                              Overloaded{
                                                                                                  [&](const typename List<
                                                                                                      std::shared_ptr<
                                                                                                          BinomialHeap::
                                                                                                              tree>>::
                                                                                                          Nil &)
                                                                                                      -> std::shared_ptr<
                                                                                                          List<std::shared_ptr<
                                                                                                              BinomialHeap::
                                                                                                                  tree>>> {
                                                                                                    return carry(
                                                                                                        p,
                                                                                                        std::move(
                                                                                                            c));
                                                                                                  },
                                                                                                  [&](const typename List<
                                                                                                      std::shared_ptr<
                                                                                                          BinomialHeap::
                                                                                                              tree>>::
                                                                                                          Cons &
                                                                                                              _args1)
                                                                                                      -> std::shared_ptr<List<std::
                                                                                                                                  shared_ptr<
                                                                                                                                      BinomialHeap::
                                                                                                                                          tree>>> {
                                                                                                    return std::visit(
                                                                                                        Overloaded{
                                                                                                            [&](const typename BinomialHeap::tree::Node
                                                                                                                    &) -> std::
                                                                                                                           shared_ptr<List<
                                                                                                                               std::shared_ptr<
                                                                                                                                   BinomialHeap::
                                                                                                                                       tree>>> {
                                                                                                                             return List<
                                                                                                                                 std::shared_ptr<
                                                                                                                                     BinomialHeap::
                                                                                                                                         tree>>::
                                                                                                                                 cons(
                                                                                                                                     c,
                                                                                                                                     join(
                                                                                                                                         _args
                                                                                                                                             .d_a1,
                                                                                                                                         _args1
                                                                                                                                             .d_a1,
                                                                                                                                         smash(
                                                                                                                                             _args
                                                                                                                                                 .d_a0,
                                                                                                                                             _args1
                                                                                                                                                 .d_a0)));
                                                                                                                           },
                                                                                                            [&](const typename BinomialHeap::
                                                                                                                    tree::Leaf
                                                                                                                        &) -> std::
                                                                                                                               shared_ptr<List<
                                                                                                                                   std::shared_ptr<
                                                                                                                                       BinomialHeap::
                                                                                                                                           tree>>> {
                                                                                                                                 return std::visit(
                                                                                                                                     Overloaded{
                                                                                                                                         [&](const typename BinomialHeap::
                                                                                                                                                 tree::Node
                                                                                                                                                     &)
                                                                                                                                             -> std::shared_ptr<
                                                                                                                                                 List<std::shared_ptr<
                                                                                                                                                     BinomialHeap::
                                                                                                                                                         tree>>> {
                                                                                                                                           return List<
                                                                                                                                               std::shared_ptr<
                                                                                                                                                   BinomialHeap::
                                                                                                                                                       tree>>::
                                                                                                                                               cons(
                                                                                                                                                   tree::
                                                                                                                                                       leaf(),
                                                                                                                                                   join(
                                                                                                                                                       _args
                                                                                                                                                           .d_a1,
                                                                                                                                                       _args1
                                                                                                                                                           .d_a1,
                                                                                                                                                       smash(
                                                                                                                                                           c,
                                                                                                                                                           _args
                                                                                                                                                               .d_a0)));
                                                                                                                                         },
                                                                                                                                         [&](const typename BinomialHeap::
                                                                                                                                                 tree::Leaf
                                                                                                                                                     &)
                                                                                                                                             -> std::shared_ptr<
                                                                                                                                                 List<std::shared_ptr<
                                                                                                                                                     BinomialHeap::
                                                                                                                                                         tree>>> {
                                                                                                                                           return List<
                                                                                                                                               std::shared_ptr<
                                                                                                                                                   BinomialHeap::
                                                                                                                                                       tree>>::
                                                                                                                                               cons(
                                                                                                                                                   _args
                                                                                                                                                       .d_a0,
                                                                                                                                                   join(
                                                                                                                                                       _args
                                                                                                                                                           .d_a1,
                                                                                                                                                       _args1
                                                                                                                                                           .d_a1,
                                                                                                                                                       tree::
                                                                                                                                                           leaf()));
                                                                                                                                         }},
                                                                                                                                     c->v());
                                                                                                                               }},
                                                                                                        _args1
                                                                                                            .d_a0
                                                                                                            ->v());
                                                                                                  }},
                                                                                              q->v());
                                                                                        },
                                                                         [&](const typename BinomialHeap::
                                                                                 tree::Leaf
                                                                                     &)
                                                                             -> std::
                                                                                 shared_ptr<List<
                                                                                     std::shared_ptr<
                                                                                         BinomialHeap::tree>>> {
                                                                                   return std::visit(
                                                                                       Overloaded{
                                                                                           [&](const typename List<
                                                                                               std::shared_ptr<
                                                                                                   BinomialHeap::
                                                                                                       tree>>::
                                                                                                   Nil &)
                                                                                               -> std::shared_ptr<
                                                                                                   List<std::shared_ptr<
                                                                                                       BinomialHeap::
                                                                                                           tree>>> {
                                                                                             return carry(
                                                                                                 p,
                                                                                                 std::move(
                                                                                                     c));
                                                                                           },
                                                                                           [&](const typename List<
                                                                                               std::shared_ptr<
                                                                                                   BinomialHeap::
                                                                                                       tree>>::
                                                                                                   Cons &
                                                                                                       _args1)
                                                                                               -> std::shared_ptr<
                                                                                                   List<std::shared_ptr<
                                                                                                       BinomialHeap::
                                                                                                           tree>>> {
                                                                                             return std::
                                                                                                 visit(
                                                                                                     Overloaded{
                                                                                                         [&](const typename BinomialHeap::tree::
                                                                                                                 Node &) -> std::
                                                                                                                             shared_ptr<List<
                                                                                                                                 std::shared_ptr<
                                                                                                                                     BinomialHeap::
                                                                                                                                         tree>>> {
                                                                                                                               return std::visit(
                                                                                                                                   Overloaded{
                                                                                                                                       [&](const typename BinomialHeap::
                                                                                                                                               tree::Node
                                                                                                                                                   &)
                                                                                                                                           -> std::shared_ptr<
                                                                                                                                               List<std::shared_ptr<
                                                                                                                                                   BinomialHeap::
                                                                                                                                                       tree>>> {
                                                                                                                                         return List<
                                                                                                                                             std::shared_ptr<
                                                                                                                                                 BinomialHeap::
                                                                                                                                                     tree>>::
                                                                                                                                             cons(
                                                                                                                                                 tree::
                                                                                                                                                     leaf(),
                                                                                                                                                 join(
                                                                                                                                                     _args
                                                                                                                                                         .d_a1,
                                                                                                                                                     _args1
                                                                                                                                                         .d_a1,
                                                                                                                                                     smash(
                                                                                                                                                         c,
                                                                                                                                                         _args1
                                                                                                                                                             .d_a0)));
                                                                                                                                       },
                                                                                                                                       [&](const typename BinomialHeap::
                                                                                                                                               tree::Leaf
                                                                                                                                                   &)
                                                                                                                                           -> std::shared_ptr<
                                                                                                                                               List<std::shared_ptr<
                                                                                                                                                   BinomialHeap::
                                                                                                                                                       tree>>> {
                                                                                                                                         return List<
                                                                                                                                             std::shared_ptr<
                                                                                                                                                 BinomialHeap::
                                                                                                                                                     tree>>::
                                                                                                                                             cons(
                                                                                                                                                 _args1
                                                                                                                                                     .d_a0,
                                                                                                                                                 join(
                                                                                                                                                     _args
                                                                                                                                                         .d_a1,
                                                                                                                                                     _args1
                                                                                                                                                         .d_a1,
                                                                                                                                                     tree::
                                                                                                                                                         leaf()));
                                                                                                                                       }},
                                                                                                                                   c->v());
                                                                                                                             },
                                                                                                         [&](const typename BinomialHeap::
                                                                                                                 tree::Leaf &) -> std::
                                                                                                                                   shared_ptr<List<
                                                                                                                                       std::shared_ptr<
                                                                                                                                           BinomialHeap::
                                                                                                                                               tree>>> {
                                                                                                                                     return List<
                                                                                                                                         std::shared_ptr<
                                                                                                                                             BinomialHeap::
                                                                                                                                                 tree>>::
                                                                                                                                         cons(
                                                                                                                                             c,
                                                                                                                                             join(
                                                                                                                                                 _args
                                                                                                                                                     .d_a1,
                                                                                                                                                 _args1
                                                                                                                                                     .d_a1,
                                                                                                                                                 tree::
                                                                                                                                                     leaf()));
                                                                                                                                   }},
                                                                                                     _args1
                                                                                                         .d_a0
                                                                                                         ->v());
                                                                                           }},
                                                                                       q->v());
                                                                                 }},
                                                                     _args.d_a0
                                                                         ->v());
                                                         }},
      p->v());
}

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::heap_delete_max(const std::shared_ptr<BinomialHeap::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename BinomialHeap::tree::Node &_args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return std::visit(
                Overloaded{
                    [](const typename BinomialHeap::tree::Node &)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<std::shared_ptr<BinomialHeap::tree>>::nil();
                    },
                    [&](const typename BinomialHeap::tree::Leaf &)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return unzip(
                          _args.d_a1,
                          [](std::shared_ptr<
                              List<std::shared_ptr<BinomialHeap::tree>>>
                                 u) { return u; });
                    }},
                _args.d_a2->v());
          },
          [](const typename BinomialHeap::tree::Leaf &)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return List<std::shared_ptr<BinomialHeap::tree>>::nil();
          }},
      t->v());
}

__attribute__((pure)) BinomialHeap::key BinomialHeap::find_max_helper(
    const unsigned int current,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil &)
              -> unsigned int { return current; },
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                  &_args) -> unsigned int {
            return std::visit(
                Overloaded{[&](const typename BinomialHeap::tree::Node &_args0)
                               -> unsigned int {
                             return find_max_helper(
                                 [&]() -> unsigned int {
                                   if (current < _args0.d_a0) {
                                     return _args0.d_a0;
                                   } else {
                                     return current;
                                   }
                                 }(),
                                 _args.d_a1);
                           },
                           [&](const typename BinomialHeap::tree::Leaf &)
                               -> unsigned int {
                             return find_max_helper(current, _args.d_a1);
                           }},
                _args.d_a0->v());
          }},
      q->v());
}

__attribute__((pure)) std::optional<BinomialHeap::key> BinomialHeap::find_max(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil &)
              -> std::optional<unsigned int> {
            return std::optional<unsigned int>();
          },
          [](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                 &_args) -> std::optional<unsigned int> {
            return std::visit(
                Overloaded{[&](const typename BinomialHeap::tree::Node &_args0)
                               -> std::optional<unsigned int> {
                             return std::make_optional<unsigned int>(
                                 find_max_helper(_args0.d_a0, _args.d_a1));
                           },
                           [&](const typename BinomialHeap::tree::Leaf &)
                               -> std::optional<unsigned int> {
                             return find_max(_args.d_a1);
                           }},
                _args.d_a0->v());
          }},
      q->v());
}

__attribute__((pure)) std::pair<BinomialHeap::priqueue, BinomialHeap::priqueue>
BinomialHeap::delete_max_aux(
    const unsigned int m,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil &)
              -> std::pair<
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>,
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>> {
            return std::make_pair(
                List<std::shared_ptr<BinomialHeap::tree>>::nil(),
                List<std::shared_ptr<BinomialHeap::tree>>::nil());
          },
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                  &_args)
              -> std::pair<
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>,
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>> {
            return std::visit(
                Overloaded{
                    [&](const typename BinomialHeap::tree::Node &_args0)
                        -> std::pair<
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>,
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>> {
                      return std::visit(
                          Overloaded{
                              [](const typename BinomialHeap::tree::Node &)
                                  -> std::pair<
                                      std::shared_ptr<List<
                                          std::shared_ptr<BinomialHeap::tree>>>,
                                      std::shared_ptr<List<std::shared_ptr<
                                          BinomialHeap::tree>>>> {
                                return std::make_pair(
                                    List<std::shared_ptr<BinomialHeap::tree>>::
                                        nil(),
                                    List<std::shared_ptr<BinomialHeap::tree>>::
                                        nil());
                              },
                              [&](const typename BinomialHeap::tree::Leaf &)
                                  -> std::pair<
                                      std::shared_ptr<List<
                                          std::shared_ptr<BinomialHeap::tree>>>,
                                      std::shared_ptr<List<std::shared_ptr<
                                          BinomialHeap::tree>>>> {
                                if (_args0.d_a0 < m) {
                                  auto _cs = delete_max_aux(m, _args.d_a1);
                                  std::shared_ptr<
                                      List<std::shared_ptr<BinomialHeap::tree>>>
                                      j = _cs.first;
                                  std::shared_ptr<
                                      List<std::shared_ptr<BinomialHeap::tree>>>
                                      k = _cs.second;
                                  return std::make_pair(
                                      List<
                                          std::shared_ptr<BinomialHeap::tree>>::
                                          cons(tree::node(_args0.d_a0,
                                                          _args0.d_a1,
                                                          tree::leaf()),
                                               j),
                                      k);
                                } else {
                                  return std::make_pair(
                                      List<
                                          std::shared_ptr<BinomialHeap::tree>>::
                                          cons(tree::leaf(), _args.d_a1),
                                      heap_delete_max(
                                          tree::node(_args0.d_a0, _args0.d_a1,
                                                     tree::leaf())));
                                }
                              }},
                          _args0.d_a2->v());
                    },
                    [&](const typename BinomialHeap::tree::Leaf &)
                        -> std::pair<
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>,
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>> {
                      auto _cs = delete_max_aux(m, _args.d_a1);
                      std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>
                          j = _cs.first;
                      std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>
                          k = _cs.second;
                      return std::make_pair(
                          List<std::shared_ptr<BinomialHeap::tree>>::cons(
                              tree::leaf(), j),
                          k);
                    }},
                _args.d_a0->v());
          }},
      p->v());
}

__attribute__((pure))
std::optional<std::pair<BinomialHeap::key, BinomialHeap::priqueue>>
BinomialHeap::delete_max(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  auto _cs = find_max(q);
  if (_cs.has_value()) {
    unsigned int m = *_cs;
    auto _cs = delete_max_aux(m, q);
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> p_ = _cs.first;
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q_ = _cs.second;
    return std::make_optional<
        std::pair<unsigned int,
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>>(
        std::make_pair(m, join(p_, q_, tree::leaf())));
  } else {
    return std::optional<std::pair<
        unsigned int,
        std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>>();
  }
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::merge(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return join(p, q, tree::leaf());
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::insert_list(
    const std::shared_ptr<List<unsigned int>> &l,
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil &)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return q;
          },
          [&](const typename List<unsigned int>::Cons &_args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return insert_list(_args.d_a1, insert(_args.d_a0, std::move(q)));
          }},
      l->v());
}

std::shared_ptr<List<unsigned int>>
BinomialHeap::make_list(const unsigned int n,
                        std::shared_ptr<List<unsigned int>> l) {
  if (n <= 0) {
    return List<unsigned int>::cons(0u, l);
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return List<unsigned int>::cons(1u, l);
    } else {
      unsigned int n1 = n0 - 1;
      return make_list(n1, List<unsigned int>::cons(((n1 + 1) + 1), l));
    }
  }
}

__attribute__((pure)) BinomialHeap::key BinomialHeap::help(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &c) {
  auto _cs = delete_max(c);
  if (_cs.has_value()) {
    std::pair<unsigned int,
              std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>
        p = *_cs;
    unsigned int k = p.first;
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> _x = p.second;
    return k;
  } else {
    return 0u;
  }
}
