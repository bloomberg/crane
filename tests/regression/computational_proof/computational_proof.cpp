#include <computational_proof.h>

#include <memory>
#include <type_traits>
#include <utility>
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
      if (s) {
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
    return n;
  } else {
    return m;
  }
}

__attribute__((pure)) unsigned int
ComputationalProof::max_dec(const unsigned int n, const unsigned int m) {
  if (le_dec(n, m)) {
    return m;
  } else {
    return n;
  }
}

std::shared_ptr<List<unsigned int>>
ComputationalProof::insert_dec(const unsigned int x,
                               const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::Nil &)
                     -> std::shared_ptr<List<unsigned int>> {
                   return List<unsigned int>::cons(x,
                                                   List<unsigned int>::nil());
                 },
                 [&](const typename List<unsigned int>::Cons &_args)
                     -> std::shared_ptr<List<unsigned int>> {
                   if (le_dec(x, _args.d_a0)) {
                     return List<unsigned int>::cons(
                         x, List<unsigned int>::cons(_args.d_a0, _args.d_a1));
                   } else {
                     return List<unsigned int>::cons(_args.d_a0,
                                                     insert_dec(x, _args.d_a1));
                   }
                 }},
      l->v());
}

std::shared_ptr<List<unsigned int>>
ComputationalProof::isort_dec(const std::shared_ptr<List<unsigned int>> &l) {
  return std::visit(
      Overloaded{[](const typename List<unsigned int>::Nil &)
                     -> std::shared_ptr<List<unsigned int>> {
                   return List<unsigned int>::nil();
                 },
                 [](const typename List<unsigned int>::Cons &_args)
                     -> std::shared_ptr<List<unsigned int>> {
                   return insert_dec(_args.d_a0, isort_dec(_args.d_a1));
                 }},
      l->v());
}
