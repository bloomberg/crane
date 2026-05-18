#include "anon_fixpoint.h"

uint64_t AnonFixpoint::sum_to(uint64_t n) {
  auto go_impl = [](auto &_self_go, uint64_t m, uint64_t acc) -> uint64_t {
    if (m <= 0) {
      return acc;
    } else {
      uint64_t p = m - 1;
      return _self_go(_self_go, p, (m + acc));
    }
  };
  auto go = [&](uint64_t m, uint64_t acc) -> uint64_t {
    return go_impl(go_impl, m, acc);
  };
  return go(n, UINT64_C(0));
}

uint64_t AnonFixpoint::factorial(uint64_t m) {
  if (m <= 0) {
    return UINT64_C(1);
  } else {
    uint64_t p = m - 1;
    return (m * factorial(p));
  }
}

uint64_t AnonFixpoint::double_sum(uint64_t m) {
  if (m <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t p = m - 1;
    auto inner_impl = [](auto &_self_inner, uint64_t k) -> uint64_t {
      if (k <= 0) {
        return UINT64_C(0);
      } else {
        uint64_t q = k - 1;
        return (UINT64_C(1) + _self_inner(_self_inner, q));
      }
    };
    auto inner = [&](uint64_t k) -> uint64_t {
      return inner_impl(inner_impl, k);
    };
    return (inner(m) + double_sum(p));
  }
}

uint64_t AnonFixpoint::gcd(uint64_t a, uint64_t b) {
  auto go_impl = [](auto &_self_go, uint64_t fuel, uint64_t x,
                    uint64_t y) -> uint64_t {
    if (fuel <= 0) {
      return x;
    } else {
      uint64_t f = fuel - 1;
      if (y <= 0) {
        return x;
      } else {
        uint64_t _x = y - 1;
        return _self_go(_self_go, f, y, (y ? x % y : x));
      }
    }
  };
  auto go = [&](uint64_t fuel, uint64_t x, uint64_t y) -> uint64_t {
    return go_impl(go_impl, fuel, x, y);
  };
  return go((a + b), a, b);
}

uint64_t AnonFixpoint::test_shadow(uint64_t n) {
  uint64_t foo = (n + n);
  auto foo0_impl = [](auto &_self_foo0, uint64_t n0) -> uint64_t {
    if (n0 <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n0 - 1;
      return (_self_foo0(_self_foo0, n_) + 1);
    }
  };
  auto foo0 = [&](uint64_t n0) -> uint64_t { return foo0_impl(foo0_impl, n0); };
  return foo0(foo);
}
