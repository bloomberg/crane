#include <computational_proof.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool
ComputationalProof::nat_eq_dec(const unsigned int &n, const unsigned int &x) {
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
ComputationalProof::nat_eqb_dec(const unsigned int &n, const unsigned int &m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) bool ComputationalProof::le_dec(const unsigned int &n,
                                                      const unsigned int &m) {
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
ComputationalProof::nat_leb_dec(const unsigned int &n, const unsigned int &m) {
  if (le_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

__attribute__((pure)) unsigned int ComputationalProof::min_dec(unsigned int n,
                                                               unsigned int m) {
  if (le_dec(n, m)) {
    return n;
  } else {
    return m;
  }
}

__attribute__((pure)) unsigned int ComputationalProof::max_dec(unsigned int n,
                                                               unsigned int m) {
  if (le_dec(n, m)) {
    return m;
  } else {
    return n;
  }
}

__attribute__((pure)) List<unsigned int>
ComputationalProof::insert_dec(unsigned int x, const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<unsigned int>::cons(x, List<unsigned int>::nil());
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    if (le_dec(x, d_a0)) {
      return List<unsigned int>::cons(x,
                                      List<unsigned int>::cons(d_a0, *(d_a1)));
    } else {
      return List<unsigned int>::cons(d_a0, insert_dec(x, *(d_a1)));
    }
  }
}

__attribute__((pure)) List<unsigned int>
ComputationalProof::isort_dec(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    return insert_dec(d_a0, isort_dec(*(d_a1)));
  }
}
