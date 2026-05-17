#include "computational_proof.h"

bool ComputationalProof::nat_eq_dec(uint64_t n, uint64_t x) {
  if (n <= 0) {
    if (x <= 0) {
      return true;
    } else {
      uint64_t _x = x - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (x <= 0) {
      return false;
    } else {
      uint64_t n1 = x - 1;
      if (nat_eq_dec(n0, n1)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool ComputationalProof::nat_eqb_dec(uint64_t n, uint64_t m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

bool ComputationalProof::le_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      bool s = le_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

bool ComputationalProof::nat_leb_dec(uint64_t n, uint64_t m) {
  if (le_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

uint64_t ComputationalProof::min_dec(uint64_t n, uint64_t m) {
  if (le_dec(n, m)) {
    return n;
  } else {
    return m;
  }
}

uint64_t ComputationalProof::max_dec(uint64_t n, uint64_t m) {
  if (le_dec(n, m)) {
    return m;
  } else {
    return n;
  }
}

List<uint64_t> ComputationalProof::insert_dec(uint64_t x,
                                              const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::cons(x, List<uint64_t>::nil());
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    if (le_dec(x, a0)) {
      return List<uint64_t>::cons(x, List<uint64_t>::cons(a0, *a1));
    } else {
      return List<uint64_t>::cons(a0, insert_dec(x, *a1));
    }
  }
}

List<uint64_t> ComputationalProof::isort_dec(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    return insert_dec(a0, isort_dec(*a1));
  }
}
