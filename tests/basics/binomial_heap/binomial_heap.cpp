#include <binomial_heap.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<BinomialHeap::tree>
BinomialHeap::smash(const std::shared_ptr<BinomialHeap::tree> &t,
                    const std::shared_ptr<BinomialHeap::tree> &u) {
  return std::visit(
      Overloaded{
          [&](const typename BinomialHeap::tree::Node _args)
              -> std::shared_ptr<BinomialHeap::tree> {
            unsigned int x = _args.d_a0;
            std::shared_ptr<BinomialHeap::tree> t1 = _args.d_a1;
            std::shared_ptr<BinomialHeap::tree> t0 = _args.d_a2;
            return std::visit(
                Overloaded{
                    [](const typename BinomialHeap::tree::Node _args)
                        -> std::shared_ptr<BinomialHeap::tree> {
                      return tree::ctor::Leaf_();
                    },
                    [&](const typename BinomialHeap::tree::Leaf _args)
                        -> std::shared_ptr<BinomialHeap::tree> {
                      return std::visit(
                          Overloaded{
                              [&](const typename BinomialHeap::tree::Node _args)
                                  -> std::shared_ptr<BinomialHeap::tree> {
                                unsigned int y = _args.d_a0;
                                std::shared_ptr<BinomialHeap::tree> u1 =
                                    _args.d_a1;
                                std::shared_ptr<BinomialHeap::tree> t2 =
                                    _args.d_a2;
                                return std::visit(
                                    Overloaded{
                                        [](const typename BinomialHeap::tree::
                                               Node _args)
                                            -> std::shared_ptr<
                                                BinomialHeap::tree> {
                                          return tree::ctor::Leaf_();
                                        },
                                        [&](const typename BinomialHeap::tree::
                                                Leaf _args)
                                            -> std::shared_ptr<
                                                BinomialHeap::tree> {
                                          if (y < x) {
                                            return tree::ctor::Node_(
                                                std::move(x),
                                                tree::ctor::Node_(
                                                    std::move(y), std::move(u1),
                                                    std::move(t1)),
                                                tree::ctor::Leaf_());
                                          } else {
                                            return tree::ctor::Node_(
                                                std::move(y),
                                                tree::ctor::Node_(
                                                    std::move(x), std::move(t1),
                                                    std::move(u1)),
                                                tree::ctor::Leaf_());
                                          }
                                        }},
                                    std::move(t2)->v());
                              },
                              [](const typename BinomialHeap::tree::Leaf _args)
                                  -> std::shared_ptr<BinomialHeap::tree> {
                                return tree::ctor::Leaf_();
                              }},
                          u->v());
                    }},
                std::move(t0)->v());
          },
          [](const typename BinomialHeap::tree::Leaf _args)
              -> std::shared_ptr<BinomialHeap::tree> {
            return tree::ctor::Leaf_();
          }},
      t->v());
}

std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> BinomialHeap::carry(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q,
    std::shared_ptr<BinomialHeap::tree> t) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil
                  _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return std::visit(
                Overloaded{
                    [&](const typename BinomialHeap::tree::Node _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<std::shared_ptr<BinomialHeap::tree>>::ctor::
                          Cons_(std::move(t),
                                List<std::shared_ptr<BinomialHeap::tree>>::
                                    ctor::Nil_());
                    },
                    [](const typename BinomialHeap::tree::Leaf _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<
                          std::shared_ptr<BinomialHeap::tree>>::ctor::Nil_();
                    }},
                t->v());
          },
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                  _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            std::shared_ptr<BinomialHeap::tree> u = _args.d_a0;
            std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q_ =
                _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename BinomialHeap::tree::Node _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return std::visit(
                          Overloaded{
                              [&](const typename BinomialHeap::tree::Node _args)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                return List<
                                    std::shared_ptr<BinomialHeap::tree>>::ctor::
                                    Cons_(tree::ctor::Leaf_(),
                                          carry(std::move(q_),
                                                smash(std::move(t),
                                                      std::move(u))));
                              },
                              [&](const typename BinomialHeap::tree::Leaf _args)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                return List<
                                    std::shared_ptr<BinomialHeap::tree>>::ctor::
                                    Cons_(std::move(u), std::move(q_));
                              }},
                          t->v());
                    },
                    [&](const typename BinomialHeap::tree::Leaf _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<std::shared_ptr<BinomialHeap::tree>>::ctor::
                          Cons_(std::move(t), std::move(q_));
                    }},
                u->v());
          }},
      q->v());
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::insert(
    const unsigned int x,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return carry(q, tree::ctor::Node_(std::move(x), tree::ctor::Leaf_(),
                                    tree::ctor::Leaf_()));
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::join(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q,
    std::shared_ptr<BinomialHeap::tree> c) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil
                  _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return carry(q, std::move(c));
          },
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                  _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            std::shared_ptr<BinomialHeap::tree> p1 = _args.d_a0;
            std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> p_ =
                _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename BinomialHeap::tree::Node _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return std::visit(
                          Overloaded{
                              [&](const typename List<std::shared_ptr<
                                      BinomialHeap::tree>>::Nil _args)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                return carry(p, std::move(c));
                              },
                              [&](const typename List<std::shared_ptr<
                                      BinomialHeap::tree>>::Cons _args)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                std::shared_ptr<BinomialHeap::tree> q1 =
                                    _args.d_a0;
                                std::shared_ptr<
                                    List<std::shared_ptr<BinomialHeap::tree>>>
                                    q_ = _args.d_a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename BinomialHeap::tree::
                                                Node _args)
                                            -> std::shared_ptr<
                                                List<std::shared_ptr<
                                                    BinomialHeap::tree>>> {
                                          return List<std::shared_ptr<
                                              BinomialHeap::tree>>::ctor::
                                              Cons_(std::move(c),
                                                    join(std::move(p_),
                                                         std::move(q_),
                                                         smash(std::move(p1),
                                                               std::move(q1))));
                                        },
                                        [&](const typename BinomialHeap::tree::
                                                Leaf _args)
                                            -> std::shared_ptr<
                                                List<std::shared_ptr<
                                                    BinomialHeap::tree>>> {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename BinomialHeap::
                                                          tree::Node _args)
                                                      -> std::shared_ptr<
                                                          List<std::shared_ptr<
                                                              BinomialHeap::
                                                                  tree>>> {
                                                    return List<std::shared_ptr<
                                                        BinomialHeap::tree>>::
                                                        ctor::Cons_(
                                                            tree::ctor::Leaf_(),
                                                            join(std::move(p_),
                                                                 std::move(q_),
                                                                 smash(
                                                                     std::move(
                                                                         c),
                                                                     std::move(
                                                                         p1))));
                                                  },
                                                  [&](const typename BinomialHeap::
                                                          tree::Leaf _args)
                                                      -> std::shared_ptr<
                                                          List<std::shared_ptr<
                                                              BinomialHeap::
                                                                  tree>>> {
                                                    return List<std::shared_ptr<
                                                        BinomialHeap::tree>>::
                                                        ctor::Cons_(
                                                            std::move(p1),
                                                            join(std::move(p_),
                                                                 std::move(q_),
                                                                 tree::ctor::
                                                                     Leaf_()));
                                                  }},
                                              c->v());
                                        }},
                                    q1->v());
                              }},
                          q->v());
                    },
                    [&](const typename BinomialHeap::tree::Leaf _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return std::visit(
                          Overloaded{
                              [&](const typename List<std::shared_ptr<
                                      BinomialHeap::tree>>::Nil _args)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                return carry(p, std::move(c));
                              },
                              [&](const typename List<std::shared_ptr<
                                      BinomialHeap::tree>>::Cons _args)
                                  -> std::shared_ptr<List<
                                      std::shared_ptr<BinomialHeap::tree>>> {
                                std::shared_ptr<BinomialHeap::tree> q1 =
                                    _args.d_a0;
                                std::shared_ptr<
                                    List<std::shared_ptr<BinomialHeap::tree>>>
                                    q_ = _args.d_a1;
                                return std::visit(
                                    Overloaded{
                                        [&](const typename BinomialHeap::tree::
                                                Node _args)
                                            -> std::shared_ptr<
                                                List<std::shared_ptr<
                                                    BinomialHeap::tree>>> {
                                          return std::visit(
                                              Overloaded{
                                                  [&](const typename BinomialHeap::
                                                          tree::Node _args)
                                                      -> std::shared_ptr<
                                                          List<std::shared_ptr<
                                                              BinomialHeap::
                                                                  tree>>> {
                                                    return List<std::shared_ptr<
                                                        BinomialHeap::tree>>::
                                                        ctor::Cons_(
                                                            tree::ctor::Leaf_(),
                                                            join(std::move(p_),
                                                                 std::move(q_),
                                                                 smash(
                                                                     std::move(
                                                                         c),
                                                                     std::move(
                                                                         q1))));
                                                  },
                                                  [&](const typename BinomialHeap::
                                                          tree::Leaf _args)
                                                      -> std::shared_ptr<
                                                          List<std::shared_ptr<
                                                              BinomialHeap::
                                                                  tree>>> {
                                                    return List<std::shared_ptr<
                                                        BinomialHeap::tree>>::
                                                        ctor::Cons_(
                                                            std::move(q1),
                                                            join(std::move(p_),
                                                                 std::move(q_),
                                                                 tree::ctor::
                                                                     Leaf_()));
                                                  }},
                                              c->v());
                                        },
                                        [&](const typename BinomialHeap::tree::
                                                Leaf _args)
                                            -> std::shared_ptr<
                                                List<std::shared_ptr<
                                                    BinomialHeap::tree>>> {
                                          return List<std::shared_ptr<
                                              BinomialHeap::tree>>::ctor::
                                              Cons_(std::move(c),
                                                    join(std::move(p_),
                                                         std::move(q_),
                                                         tree::ctor::Leaf_()));
                                        }},
                                    q1->v());
                              }},
                          q->v());
                    }},
                p1->v());
          }},
      p->v());
}

__attribute__((pure)) BinomialHeap::priqueue
BinomialHeap::heap_delete_max(const std::shared_ptr<BinomialHeap::tree> &t) {
  return std::visit(
      Overloaded{
          [](const typename BinomialHeap::tree::Node _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            std::shared_ptr<BinomialHeap::tree> t1 = _args.d_a1;
            std::shared_ptr<BinomialHeap::tree> t0 = _args.d_a2;
            return std::visit(
                Overloaded{
                    [](const typename BinomialHeap::tree::Node _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return List<
                          std::shared_ptr<BinomialHeap::tree>>::ctor::Nil_();
                    },
                    [&](const typename BinomialHeap::tree::Leaf _args)
                        -> std::shared_ptr<
                            List<std::shared_ptr<BinomialHeap::tree>>> {
                      return unzip(
                          std::move(t1),
                          [](std::shared_ptr<
                              List<std::shared_ptr<BinomialHeap::tree>>>
                                 u) { return u; });
                    }},
                std::move(t0)->v());
          },
          [](const typename BinomialHeap::tree::Leaf _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return List<std::shared_ptr<BinomialHeap::tree>>::ctor::Nil_();
          }},
      t->v());
}

__attribute__((pure)) BinomialHeap::key BinomialHeap::find_max_helper(
    const unsigned int current,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return std::visit(
      Overloaded{
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil
                  _args) -> unsigned int { return std::move(current); },
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                  _args) -> unsigned int {
            std::shared_ptr<BinomialHeap::tree> t = _args.d_a0;
            std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q_ =
                _args.d_a1;
            return std::visit(
                Overloaded{[&](const typename BinomialHeap::tree::Node _args)
                               -> unsigned int {
                             unsigned int x = _args.d_a0;
                             return find_max_helper(
                                 [&](void) {
                                   if (current < x) {
                                     return std::move(x);
                                   } else {
                                     return std::move(current);
                                   }
                                 }(),
                                 std::move(q_));
                           },
                           [&](const typename BinomialHeap::tree::Leaf _args)
                               -> unsigned int {
                             return find_max_helper(std::move(current),
                                                    std::move(q_));
                           }},
                std::move(t)->v());
          }},
      q->v());
}

__attribute__((pure)) std::optional<BinomialHeap::key> BinomialHeap::find_max(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil
                 _args) -> std::optional<unsigned int> { return std::nullopt; },
          [](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                 _args) -> std::optional<unsigned int> {
            std::shared_ptr<BinomialHeap::tree> t = _args.d_a0;
            std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q_ =
                _args.d_a1;
            return std::visit(
                Overloaded{[&](const typename BinomialHeap::tree::Node _args)
                               -> std::optional<unsigned int> {
                             unsigned int x = _args.d_a0;
                             return std::make_optional<unsigned int>(
                                 find_max_helper(std::move(x), std::move(q_)));
                           },
                           [&](const typename BinomialHeap::tree::Leaf _args)
                               -> std::optional<unsigned int> {
                             return find_max(std::move(q_));
                           }},
                std::move(t)->v());
          }},
      q->v());
}

__attribute__((pure)) std::pair<BinomialHeap::priqueue, BinomialHeap::priqueue>
BinomialHeap::delete_max_aux(
    const unsigned int m,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<BinomialHeap::tree>>::Nil
                 _args)
              -> std::pair<
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>,
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>> {
            return std::make_pair(
                List<std::shared_ptr<BinomialHeap::tree>>::ctor::Nil_(),
                List<std::shared_ptr<BinomialHeap::tree>>::ctor::Nil_());
          },
          [&](const typename List<std::shared_ptr<BinomialHeap::tree>>::Cons
                  _args)
              -> std::pair<
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>,
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>> {
            std::shared_ptr<BinomialHeap::tree> t = _args.d_a0;
            std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> p_ =
                _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename BinomialHeap::tree::Node _args)
                        -> std::pair<
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>,
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>> {
                      unsigned int x = _args.d_a0;
                      std::shared_ptr<BinomialHeap::tree> t1 = _args.d_a1;
                      std::shared_ptr<BinomialHeap::tree> t0 = _args.d_a2;
                      return std::visit(
                          Overloaded{
                              [](const typename BinomialHeap::tree::Node _args)
                                  -> std::pair<
                                      std::shared_ptr<List<
                                          std::shared_ptr<BinomialHeap::tree>>>,
                                      std::shared_ptr<List<std::shared_ptr<
                                          BinomialHeap::tree>>>> {
                                return std::make_pair(
                                    List<std::shared_ptr<BinomialHeap::tree>>::
                                        ctor::Nil_(),
                                    List<std::shared_ptr<BinomialHeap::tree>>::
                                        ctor::Nil_());
                              },
                              [&](const typename BinomialHeap::tree::Leaf _args)
                                  -> std::pair<
                                      std::shared_ptr<List<
                                          std::shared_ptr<BinomialHeap::tree>>>,
                                      std::shared_ptr<List<std::shared_ptr<
                                          BinomialHeap::tree>>>> {
                                if (x < m) {
                                  std::shared_ptr<
                                      List<std::shared_ptr<BinomialHeap::tree>>>
                                      j = delete_max_aux(m, p_).first;
                                  std::shared_ptr<
                                      List<std::shared_ptr<BinomialHeap::tree>>>
                                      k = delete_max_aux(m, p_).second;
                                  return std::make_pair(
                                      List<
                                          std::shared_ptr<BinomialHeap::tree>>::
                                          ctor::Cons_(tree::ctor::Node_(
                                                          std::move(x),
                                                          std::move(t1),
                                                          tree::ctor::Leaf_()),
                                                      std::move(j)),
                                      std::move(k));
                                } else {
                                  return std::make_pair(
                                      List<
                                          std::shared_ptr<BinomialHeap::tree>>::
                                          ctor::Cons_(tree::ctor::Leaf_(),
                                                      std::move(p_)),
                                      heap_delete_max(tree::ctor::Node_(
                                          std::move(x), std::move(t1),
                                          tree::ctor::Leaf_())));
                                }
                              }},
                          std::move(t0)->v());
                    },
                    [&](const typename BinomialHeap::tree::Leaf _args)
                        -> std::pair<
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>,
                            std::shared_ptr<
                                List<std::shared_ptr<BinomialHeap::tree>>>> {
                      std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>
                          j = delete_max_aux(m, p_).first;
                      std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>
                          k = delete_max_aux(m, p_).second;
                      return std::make_pair(
                          List<std::shared_ptr<BinomialHeap::tree>>::ctor::
                              Cons_(tree::ctor::Leaf_(), std::move(j)),
                          std::move(k));
                    }},
                std::move(t)->v());
          }},
      p->v());
}

__attribute__((pure))
std::optional<std::pair<BinomialHeap::key, BinomialHeap::priqueue>>
BinomialHeap::delete_max(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  if (find_max(q).has_value()) {
    unsigned int m = *find_max(q);
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> p_ =
        delete_max_aux(m, q).first;
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q_ =
        delete_max_aux(m, q).second;
    return std::make_optional<
        std::pair<unsigned int,
                  std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>>(
        std::make_pair(m, join(p_, q_, tree::ctor::Leaf_())));
  } else {
    return std::nullopt;
  }
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::merge(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &p,
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &q) {
  return join(p, q, tree::ctor::Leaf_());
}

__attribute__((pure)) BinomialHeap::priqueue BinomialHeap::insert_list(
    const std::shared_ptr<List<unsigned int>> &l,
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> q) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            return std::move(q);
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> {
            unsigned int x = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l0 = _args.d_a1;
            return insert_list(std::move(l0),
                               insert(std::move(x), std::move(q)));
          }},
      l->v());
}

std::shared_ptr<List<unsigned int>>
BinomialHeap::make_list(const unsigned int n,
                        std::shared_ptr<List<unsigned int>> l) {
  if (n <= 0) {
    return List<unsigned int>::ctor::Cons_(0u, std::move(l));
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return List<unsigned int>::ctor::Cons_(1u, l);
    } else {
      unsigned int n1 = n0 - 1;
      return make_list(std::move(n1), List<unsigned int>::ctor::Cons_(
                                          ((std::move(n1) + 1) + 1), l));
    }
  }
}

__attribute__((pure)) BinomialHeap::key BinomialHeap::help(
    const std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> &c) {
  if (delete_max(c).has_value()) {
    std::pair<unsigned int,
              std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>>>
        p = *delete_max(c);
    unsigned int k = p.first;
    std::shared_ptr<List<std::shared_ptr<BinomialHeap::tree>>> _x = p.second;
    return k;
  } else {
    return 0u;
  }
}
