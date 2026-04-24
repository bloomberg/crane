#include <opaque.h>

#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int Opaque::safe_pred(const unsigned int &n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n0 = n - 1;
    return n0;
  }
}

__attribute__((pure)) unsigned int Opaque::pred_of_succ(unsigned int n) {
  return safe_pred((n + 1));
}

__attribute__((pure)) bool Opaque::nat_eq_dec(const unsigned int &n,
                                              const unsigned int &x) {
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

__attribute__((pure)) bool Opaque::are_equal(const unsigned int &n,
                                             const unsigned int &m) {
  if (nat_eq_dec(n, m)) {
    return true;
  } else {
    return false;
  }
}

Sig<unsigned int> Opaque::bounded_add(const unsigned int &,
                                      const unsigned int &,
                                      const unsigned int &) {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.opaque.Opaque.Opaque.bounded_add");
}
