#include <sort.h>

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

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::sort_cons_prog(const unsigned int a,
                     const std::shared_ptr<List<unsigned int>> &_x,
                     const std::shared_ptr<List<unsigned int>> &l_) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args) -> auto {
            return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
                List<unsigned int>::ctor::Cons_(
                    std::move(a), List<unsigned int>::ctor::Nil_()));
          },
          [&](const typename List<unsigned int>::Cons _args) -> auto {
            auto y = _args.d_a0;
            auto l = _args.d_a1;
            std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> s =
                sort_cons_prog(std::move(a), l, l);
            return std::visit(
                Overloaded{
                    [&](const typename Sig<
                        std::shared_ptr<List<unsigned int>>>::Exist _args)
                        -> std::shared_ptr<
                            Sig<std::shared_ptr<List<unsigned int>>>> {
                      std::shared_ptr<List<unsigned int>> x = _args.d_a0;
                      bool s0 = Compare_dec::le_lt_dec(std::move(a), y);
                      if (std::move(s0)) {
                        return Sig<std::shared_ptr<List<unsigned int>>>::ctor::
                            Exist_(List<unsigned int>::ctor::Cons_(
                                std::move(a), List<unsigned int>::ctor::Cons_(
                                                  y, std::move(l))));
                      } else {
                        return Sig<std::shared_ptr<List<unsigned int>>>::ctor::
                            Exist_(List<unsigned int>::ctor::Cons_(
                                y, std::move(x)));
                      }
                    }},
                std::move(s)->v());
          }},
      l_->v());
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::isort(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args) -> auto {
            return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
                List<unsigned int>::ctor::Nil_());
          },
          [](const typename List<unsigned int>::Cons _args) -> auto {
            unsigned int y = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l0 = _args.d_a1;
            return std::visit(
                Overloaded{
                    [&](const typename Sig<
                        std::shared_ptr<List<unsigned int>>>::Exist _args)
                        -> std::shared_ptr<
                            Sig<std::shared_ptr<List<unsigned int>>>> {
                      std::shared_ptr<List<unsigned int>> x = _args.d_a0;
                      return sort_cons_prog(std::move(y), std::move(l0),
                                            std::move(x));
                    }},
                isort(l0)->v());
          }},
      l->v());
}

std::shared_ptr<List<unsigned int>>
Sort::merge(std::shared_ptr<List<unsigned int>> l1,
            const std::shared_ptr<List<unsigned int>> &l2) {
  std::function<std::shared_ptr<List<unsigned int>>(
      std::shared_ptr<List<unsigned int>>)>
      merge_aux;
  merge_aux = [&](std::shared_ptr<List<unsigned int>> l3)
      -> std::shared_ptr<List<unsigned int>> {
    return std::visit(
        Overloaded{
            [&](const typename List<unsigned int>::Nil _args)
                -> std::shared_ptr<List<unsigned int>> {
              return std::move(l3);
            },
            [&](const typename List<unsigned int>::Cons _args)
                -> std::shared_ptr<List<unsigned int>> {
              unsigned int a1 = _args.d_a0;
              std::shared_ptr<List<unsigned int>> l1_ = _args.d_a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::Nil _args)
                          -> std::shared_ptr<List<unsigned int>> { return l1; },
                      [&](const typename List<unsigned int>::Cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        unsigned int a2 = _args.d_a0;
                        std::shared_ptr<List<unsigned int>> l2_ = _args.d_a1;
                        if (Compare_dec::le_lt_dec(a1, a2)) {
                          return List<unsigned int>::ctor::Cons_(
                              std::move(a1),
                              merge(std::move(l1_), std::move(l3)));
                        } else {
                          return List<unsigned int>::ctor::Cons_(
                              std::move(a2), merge_aux(std::move(l2_)));
                        }
                      }},
                  l3->v());
            }},
        l1->v());
  };
  return merge_aux(l2);
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::merge_prog(const std::shared_ptr<List<unsigned int>> &_x,
                 std::shared_ptr<List<unsigned int>> l1,
                 std::shared_ptr<List<unsigned int>> l2) {
  return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
      merge(std::move(l1), std::move(l2)));
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::msort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_split(
      Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
          List<unsigned int>::ctor::Nil_()),
      [](unsigned int a) {
        return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
            List<unsigned int>::ctor::Cons_(a,
                                            List<unsigned int>::ctor::Nil_()));
      },
      [](std::shared_ptr<List<unsigned int>> ls,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x0) {
        return std::visit(
            Overloaded{[&](const typename Sig<
                           std::shared_ptr<List<unsigned int>>>::Exist _args)
                           -> std::shared_ptr<
                               Sig<std::shared_ptr<List<unsigned int>>>> {
              std::shared_ptr<List<unsigned int>> x1 = _args.d_a0;
              return std::visit(
                  Overloaded{
                      [&](const typename Sig<
                          std::shared_ptr<List<unsigned int>>>::Exist _args)
                          -> std::shared_ptr<
                              Sig<std::shared_ptr<List<unsigned int>>>> {
                        std::shared_ptr<List<unsigned int>> x2 = _args.d_a0;
                        return merge_prog(ls, std::move(x1), std::move(x2));
                      }},
                  x0->v());
            }},
            x->v());
      },
      _x0);
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                      const std::shared_ptr<List<unsigned int>> &_x1,
                      std::shared_ptr<List<unsigned int>> l_,
                      std::shared_ptr<List<unsigned int>> l_0) {
  return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
      merge(std::move(l_0), std::move(l_)));
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::psort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_pair(
      Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
          List<unsigned int>::ctor::Nil_()),
      [](unsigned int a) {
        return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
            List<unsigned int>::ctor::Cons_(a,
                                            List<unsigned int>::ctor::Nil_()));
      },
      [](unsigned int a1, unsigned int a2) {
        bool s = Compare_dec::le_lt_dec(a1, a2);
        if (std::move(s)) {
          return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
              List<unsigned int>::ctor::Cons_(
                  a1, List<unsigned int>::ctor::Cons_(
                          a2, List<unsigned int>::ctor::Nil_())));
        } else {
          return Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
              List<unsigned int>::ctor::Cons_(
                  a2, List<unsigned int>::ctor::Cons_(
                          a1, List<unsigned int>::ctor::Nil_())));
        }
      },
      [](unsigned int a1, unsigned int a2,
         std::shared_ptr<List<unsigned int>> l,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x0) {
        return std::visit(
            Overloaded{[&](const typename Sig<
                           std::shared_ptr<List<unsigned int>>>::Exist _args)
                           -> std::shared_ptr<
                               Sig<std::shared_ptr<List<unsigned int>>>> {
              std::shared_ptr<List<unsigned int>> x1 = _args.d_a0;
              return std::visit(
                  Overloaded{
                      [&](const typename Sig<
                          std::shared_ptr<List<unsigned int>>>::Exist _args)
                          -> std::shared_ptr<
                              Sig<std::shared_ptr<List<unsigned int>>>> {
                        std::shared_ptr<List<unsigned int>> x2 = _args.d_a0;
                        return pair_merge_prog(a1, a2, l, std::move(x2),
                                               std::move(x1));
                      }},
                  x0->v());
            }},
            x->v());
      },
      _x0);
}

std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>>
Sort::qsort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_pivot(
      Compare_dec::le_dec,
      Sig<std::shared_ptr<List<unsigned int>>>::ctor::Exist_(
          List<unsigned int>::ctor::Nil_()),
      [](unsigned int a, std::shared_ptr<List<unsigned int>> _x,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig<std::shared_ptr<List<unsigned int>>>> x0) {
        return std::visit(
            Overloaded{[&](const typename Sig<
                           std::shared_ptr<List<unsigned int>>>::Exist _args)
                           -> std::shared_ptr<
                               Sig<std::shared_ptr<List<unsigned int>>>> {
              std::shared_ptr<List<unsigned int>> x1 = _args.d_a0;
              return std::visit(
                  Overloaded{
                      [&](const typename Sig<
                          std::shared_ptr<List<unsigned int>>>::Exist _args)
                          -> std::shared_ptr<
                              Sig<std::shared_ptr<List<unsigned int>>>> {
                        std::shared_ptr<List<unsigned int>> x2 = _args.d_a0;
                        return Sig<std::shared_ptr<List<unsigned int>>>::ctor::
                            Exist_(merge(std::move(x1),
                                         List<unsigned int>::ctor::Cons_(
                                             a, std::move(x2))));
                      }},
                  x0->v());
            }},
            x->v());
      },
      _x0);
}

__attribute__((pure)) bool Compare_dec::le_lt_dec(const unsigned int n,
                                                  const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      if (Compare_dec::le_lt_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

__attribute__((pure)) bool Compare_dec::le_gt_dec(const unsigned int _x0,
                                                  const unsigned int _x1) {
  return Compare_dec::le_lt_dec(_x0, _x1);
}

__attribute__((pure)) bool Compare_dec::le_dec(const unsigned int n,
                                               const unsigned int m) {
  bool s = Compare_dec::le_gt_dec(n, m);
  if (std::move(s)) {
    return true;
  } else {
    return false;
  }
}
