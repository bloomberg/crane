#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <isort.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>>
Sort::sort_cons_prog(const unsigned int a,
                     const std::shared_ptr<List<unsigned int>> &_x,
                     const std::shared_ptr<List<unsigned int>> &l_) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::nil _args) -> auto {
            return List<unsigned int>::ctor::cons_(
                std::move(a), List<unsigned int>::ctor::nil_());
          },
          [&](const typename List<unsigned int>::cons _args) -> auto {
            T1 y = _args._a0;
            std::shared_ptr<List<T1>> l = _args._a1;
            std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>> s =
                sort_cons_prog(std::move(a), l, l);
            bool s0 = Compare_dec::le_lt_dec(std::move(a), y);
            if (s0) {
              return List<unsigned int>::ctor::cons_(
                  std::move(a),
                  List<unsigned int>::ctor::cons_(y, std::move(l)));
            } else {
              return List<unsigned int>::ctor::cons_(y, std::move(s));
            }
          }},
      l_->v());
}

std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>>
Sort::isort(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::nil _args) -> auto {
                   return List<unsigned int>::ctor::nil_();
                 },
                 [](const typename List<unsigned int>::cons _args) -> auto {
                   unsigned int y = _args._a0;
                   std::shared_ptr<List<unsigned int>> l0 = _args._a1;
                   return sort_cons_prog(std::move(y), l0, isort(l0));
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
            [&](const typename List<unsigned int>::nil _args)
                -> std::shared_ptr<List<unsigned int>> {
              return std::move(l3);
            },
            [&](const typename List<unsigned int>::cons _args)
                -> std::shared_ptr<List<unsigned int>> {
              unsigned int a1 = _args._a0;
              std::shared_ptr<List<unsigned int>> l1_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<unsigned int>::nil _args)
                          -> std::shared_ptr<List<unsigned int>> { return l1; },
                      [&](const typename List<unsigned int>::cons _args)
                          -> std::shared_ptr<List<unsigned int>> {
                        unsigned int a2 = _args._a0;
                        std::shared_ptr<List<unsigned int>> l2_ = _args._a1;
                        if (Compare_dec::le_lt_dec(a1, a2)) {
                          return List<unsigned int>::ctor::cons_(
                              std::move(a1),
                              merge(std::move(l1_), std::move(l3)));
                        } else {
                          return List<unsigned int>::ctor::cons_(
                              std::move(a2), merge_aux(std::move(l2_)));
                        }
                      }},
                  l3->v());
            }},
        l1->v());
  };
  return merge_aux(l2);
}

std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>>
Sort::merge_prog(const std::shared_ptr<List<unsigned int>> &_x,
                 const std::shared_ptr<List<unsigned int>> &_x0,
                 const std::shared_ptr<List<unsigned int>> &_x1) {
  return merge(_x0, _x1);
}

std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>>
Sort::msort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_split(
      List<unsigned int>::ctor::nil_(),
      [](unsigned int a) {
        return List<unsigned int>::ctor::cons_(
            a, List<unsigned int>::ctor::nil_());
      },
      merge_prog)(_x0);
}

std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>>
Sort::pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                      const std::shared_ptr<List<unsigned int>> &_x1,
                      const std::shared_ptr<List<unsigned int>> &l_,
                      const std::shared_ptr<List<unsigned int>> &l_0) {
  return merge(l_0, l_);
}

std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>>
Sort::psort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_pair(
      List<unsigned int>::ctor::nil_(),
      [](unsigned int a) {
        return List<unsigned int>::ctor::cons_(
            a, List<unsigned int>::ctor::nil_());
      },
      [](unsigned int a1, unsigned int a2) {
        bool s = Compare_dec::le_lt_dec(a1, a2);
        if (s) {
          return List<unsigned int>::ctor::cons_(
              a1, List<unsigned int>::ctor::cons_(
                      a2, List<unsigned int>::ctor::nil_()));
        } else {
          return List<unsigned int>::ctor::cons_(
              a2, List<unsigned int>::ctor::cons_(
                      a1, List<unsigned int>::ctor::nil_()));
        }
      },
      [](unsigned int a1, unsigned int a2,
         std::shared_ptr<List<unsigned int>> l,
         std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>> x0) {
        return pair_merge_prog(a1, a2, l, x0, x);
      })(_x0);
}

std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>>
Sort::qsort(const std::shared_ptr<List<unsigned int>> &_x0) {
  return div_conq_pivot(
      Compare_dec::le_dec, List<unsigned int>::ctor::nil_(),
      [](unsigned int a, std::shared_ptr<List<unsigned int>> _x,
         std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>> x,
         std::shared_ptr<Sig0<std::shared_ptr<List<unsigned int>>>> x0) {
        return merge(x, List<unsigned int>::ctor::cons_(a, x0));
      })(_x0);
}

bool Compare_dec::le_lt_dec(const unsigned int n, const unsigned int m) {
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

bool Compare_dec::le_gt_dec(const unsigned int _x0, const unsigned int _x1) {
  return Compare_dec::le_lt_dec(_x0, _x1);
}

bool Compare_dec::le_dec(const unsigned int n, const unsigned int m) {
  bool s = Compare_dec::le_gt_dec(n, m);
  if (s) {
    return true;
  } else {
    return false;
  }
}
