#include <algorithm>
#include <functional>
#include <iostream>
#include <isort.h>
#include <memory>
#include <optional>
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

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
sort_cons_prog(const unsigned int a,
               const std::shared_ptr<List::list<unsigned int>> &_x,
               const std::shared_ptr<List::list<unsigned int>> &l_) {
  return std::visit(
      Overloaded{[&](const typename List::list<T1>::nil _args) -> T2 {
                   return List::list<unsigned int>::ctor::cons_(
                       a, List::list<unsigned int>::ctor::nil_());
                 },
                 [&](const typename List::list<T1>::cons _args) -> T2 {
                   T1 y = _args._a0;
                   std::shared_ptr<List::list<T1>> l = _args._a1;
                   std::shared_ptr<
                       Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
                       s = sort_cons_prog(a, l, l);
                   bool s = le_lt_dec(a, y);
                   if (s0) {
                     return List::list<unsigned int>::ctor::cons_(
                         a, List::list<unsigned int>::ctor::cons_(y, l));
                   } else {
                     return List::list<unsigned int>::ctor::cons_(y, s);
                   }
                 }},
      l_->v());
}

std::shared_ptr<Sig0::sig0<std::shared_ptr<List::list<unsigned int>>>>
isort(const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(
      Overloaded{[&](const typename List::list<T1>::nil _args) -> T2 {
                   return List::list<unsigned int>::ctor::nil_();
                 },
                 [&](const typename List::list<T1>::cons _args) -> T2 {
                   T1 y = _args._a0;
                   std::shared_ptr<List::list<T1>> l0 = _args._a1;
                   return sort_cons_prog(y, l0, isort(l0));
                 }},
      l->v());
}
