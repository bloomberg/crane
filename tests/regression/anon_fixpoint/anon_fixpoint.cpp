#include "anon_fixpoint.h"

unsigned int AnonFixpoint::sum_to(const unsigned int n) {
  auto go_impl = [](auto &_self_go, unsigned int m,
                    unsigned int acc) -> unsigned int {
    if (m <= 0) {
      return acc;
    } else {
      unsigned int p = m - 1;
      return _self_go(_self_go, p, (m + acc));
    }
  };
  std::function<unsigned int(unsigned int, unsigned int)> go =
      [&](unsigned int m, unsigned int acc) -> unsigned int {
    return go_impl(go_impl, m, acc);
  };
  return go(n, 0u);
}

unsigned int AnonFixpoint::factorial(const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int p = m - 1;
    return (m * factorial(p));
  }
}

unsigned int AnonFixpoint::double_sum(const unsigned int m) {
  if (m <= 0) {
    return 0u;
  } else {
    unsigned int p = m - 1;
    auto inner_impl = [](auto &_self_inner, unsigned int k) -> unsigned int {
      if (k <= 0) {
        return 0u;
      } else {
        unsigned int q = k - 1;
        return (1u + _self_inner(_self_inner, q));
      }
    };
    std::function<unsigned int(unsigned int)> inner =
        [&](unsigned int k) -> unsigned int {
      return inner_impl(inner_impl, k);
    };
    return (inner(m) + double_sum(p));
  }
}

unsigned int AnonFixpoint::gcd(const unsigned int a, const unsigned int b) {
  auto go_impl = [](auto &_self_go, unsigned int fuel, unsigned int x,
                    unsigned int y) -> unsigned int {
    if (fuel <= 0) {
      return x;
    } else {
      unsigned int f = fuel - 1;
      if (y <= 0) {
        return x;
      } else {
        unsigned int _x = y - 1;
        return _self_go(_self_go, f, y, (y ? x % y : x));
      }
    }
  };
  std::function<unsigned int(unsigned int, unsigned int, unsigned int)> go =
      [&](unsigned int fuel, unsigned int x, unsigned int y) -> unsigned int {
    return go_impl(go_impl, fuel, x, y);
  };
  return go((a + b), a, b);
}

unsigned int AnonFixpoint::test_shadow(const unsigned int n) {
  unsigned int foo = (n + n);
  auto foo0_impl = [](auto &_self_foo0, unsigned int n0) -> unsigned int {
    if (n0 <= 0) {
      return 0u;
    } else {
      unsigned int n_ = n0 - 1;
      return (_self_foo0(_self_foo0, n_) + 1);
    }
  };
  std::function<unsigned int(unsigned int)> foo0 =
      [&](unsigned int n0) -> unsigned int { return foo0_impl(foo0_impl, n0); };
  return foo0(foo);
}
