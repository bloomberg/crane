#include <computational_proof.h>

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

__attribute__((pure)) bool
ComputationalProof::nat_eq_dec(const unsigned int n, const unsigned int x) {
  if (n <= 0) {
    if (x <= 0) {
      return true;
    } else {
      unsigned int _x = x - 1;
      return false;
    }
  } else {
    unsigned int n0 = n - 1;
    if (x <= 0) {
      return false;
    } else {
      unsigned int n1 = x - 1;
      if (nat_eq_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

__attribute__((pure)) bool
ComputationalProof::nat_eqb_dec(const unsigned int n, const unsigned int m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool ComputationalProof::le_dec(const unsigned int n,
                                                      const unsigned int m) {
  if (n <= 0) {
    return true;
  } else {
    unsigned int n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      unsigned int n1 = m - 1;
      bool s = le_dec(n0, n1);
      if (std::move(s)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

__attribute__((pure)) bool
ComputationalProof::nat_leb_dec(const unsigned int n, const unsigned int m) {
  if (le_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) unsigned int
ComputationalProof::min_dec(const unsigned int n, const unsigned int m) {
  if (le_dec(n, m)) {
    return std::move(n);
  } else {
    return std::move(m);
  }
}

__attribute__((pure)) unsigned int
ComputationalProof::max_dec(const unsigned int n, const unsigned int m) {
  if (le_dec(n, m)) {
    return std::move(m);
  } else {
    return std::move(n);
  }
}

std::shared_ptr<List<unsigned int>>
ComputationalProof::insert_dec(const unsigned int x,
                               const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::Nil _args)
                     -> std::shared_ptr<List<unsigned int>> {
                   return List<unsigned int>::ctor::Cons_(
                       std::move(x), List<unsigned int>::ctor::Nil_());
                 },
                 [&](const typename List<unsigned int>::Cons _args)
                     -> std::shared_ptr<List<unsigned int>> {
                   unsigned int y = _args.d_a0;
                   std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
                   if (le_dec(x, y)) {
                     return List<unsigned int>::ctor::Cons_(
                         std::move(x), List<unsigned int>::ctor::Cons_(
                                           std::move(y), std::move(rest)));
                   } else {
                     return List<unsigned int>::ctor::Cons_(
                         std::move(y),
                         insert_dec(std::move(x), std::move(rest)));
                   }
                 }},
      l->v());
}

std::shared_ptr<List<unsigned int>>
ComputationalProof::isort_dec(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil _args)
                     -> std::shared_ptr<List<unsigned int>> {
                   return List<unsigned int>::ctor::Nil_();
                 },
                 [](const typename List<unsigned int>::Cons _args)
                     -> std::shared_ptr<List<unsigned int>> {
                   unsigned int x = _args.d_a0;
                   std::shared_ptr<List<unsigned int>> rest = _args.d_a1;
                   return insert_dec(std::move(x), isort_dec(std::move(rest)));
                 }},
      l->v());
}
