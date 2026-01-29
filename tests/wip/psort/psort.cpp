#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <psort.h>
#include <string>
#include <utility>
#include <variant>

bool le_lt_dec(const unsigned int n, const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      if (le_lt_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

std::shared_ptr<List::list<unsigned int>>
merge(const std::shared_ptr<List::list<unsigned int>> &l1,
      const std::shared_ptr<List::list<unsigned int>> &l2) {
  std::function<std::shared_ptr<List::list<unsigned int>>(
      std::shared_ptr<List::list<unsigned int>>)>
      merge_aux;
  merge_aux = [&](std::shared_ptr<List::list<unsigned int>> l3)
      -> std::shared_ptr<List::list<unsigned int>> {
    return std::visit(
        Overloaded{
            [&](const typename List::list<unsigned int>::nil _args)
                -> std::shared_ptr<List::list<unsigned int>> { return l3; },
            [&](const typename List::list<unsigned int>::cons _args)
                -> std::shared_ptr<List::list<unsigned int>> {
              unsigned int a1 = _args._a0;
              std::shared_ptr<List::list<unsigned int>> l1_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List::list<unsigned int>::nil _args)
                          -> std::shared_ptr<List::list<unsigned int>> {
                        return l1;
                      },
                      [&](const typename List::list<unsigned int>::cons _args)
                          -> std::shared_ptr<List::list<unsigned int>> {
                        unsigned int a2 = _args._a0;
                        std::shared_ptr<List::list<unsigned int>> l2_ =
                            _args._a1;
                        if (le_lt_dec(a1, a2)) {
                          return List::list<unsigned int>::ctor::cons_(
                              a1, merge(l1_, l3));
                        } else {
                          return List::list<unsigned int>::ctor::cons_(
                              a2, merge_aux(l2_));
                        }
                      }},
                  l3->v());
            }},
        l1->v());
  };
  return merge_aux(l2);
}

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
pair_merge_prog(const unsigned int _x, const unsigned int _x0,
                const std::shared_ptr<List::list<unsigned int>> &_x1,
                const std::shared_ptr<List::list<unsigned int>> &l_,
                const std::shared_ptr<List::list<unsigned int>> &l_0) {
  return merge(l_0, l_);
}

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
psort(const std::shared_ptr<List::list<unsigned int>> &_x0) {
  return [](const std::shared_ptr<List::list<T1>> _x0) {
    return div_conq_pair<unsigned int>(
        List::list<unsigned int>::ctor::nil_(),
        [](unsigned int a) {
          return List::list<unsigned int>::ctor::cons_(
              a, List::list<unsigned int>::ctor::nil_());
        },
        [](unsigned int a1, unsigned int a2) {
          bool s = le_lt_dec(a1, a2);
          if (s) {
            return List::list<unsigned int>::ctor::cons_(
                a1, List::list<unsigned int>::ctor::cons_(
                        a2, List::list<unsigned int>::ctor::nil_()));
          } else {
            return List::list<unsigned int>::ctor::cons_(
                a2, List::list<unsigned int>::ctor::cons_(
                        a1, List::list<unsigned int>::ctor::nil_()));
          }
        },
        [](unsigned int a1, unsigned int a2,
           std::shared_ptr<List::list<unsigned int>> l,
           std::shared_ptr<
               Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
               x,
           std::shared_ptr<
               Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
               x0) { return pair_merge_prog(a1, a2, l, x0, x); },
        _x0);
  }(_x0);
}
