#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <msort.h>
#include <optional>
#include <stdexcept>
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
merge(std::shared_ptr<List::list<unsigned int>> l1,
      const std::shared_ptr<List::list<unsigned int>> &l2) {
  std::function<std::shared_ptr<List::list<unsigned int>>(
      std::shared_ptr<List::list<unsigned int>>)>
      merge_aux;
  merge_aux = [&](std::shared_ptr<List::list<unsigned int>> l3)
      -> std::shared_ptr<List::list<unsigned int>> {
    return std::visit(
        Overloaded{
            [&](const typename List::list<unsigned int>::nil _args)
                -> std::shared_ptr<List::list<unsigned int>> {
              return std::move(l3);
            },
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
                              std::move(a1),
                              merge(std::move(l1_), std::move(l3)));
                        } else {
                          return List::list<unsigned int>::ctor::cons_(
                              std::move(a2), merge_aux(std::move(l2_)));
                        }
                      }},
                  l3->v());
            }},
        l1->v());
  };
  return merge_aux(l2);
}

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
merge_prog(const std::shared_ptr<List::list<unsigned int>> &_x,
           const std::shared_ptr<List::list<unsigned int>> &_x0,
           const std::shared_ptr<List::list<unsigned int>> &_x1) {
  return merge(_x0, _x1);
}

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
msort(const std::shared_ptr<List::list<unsigned int>> &_x0) {
  return [](const std::shared_ptr<List::list<T1>> _x0) {
    return div_conq_split<unsigned int>(
        List::list<unsigned int>::ctor::nil_(),
        [](unsigned int a) {
          return List::list<unsigned int>::ctor::cons_(
              a, List::list<unsigned int>::ctor::nil_());
        },
        merge_prog, _x0);
  }(_x0);
}
