#include "anon_fixpoint.h"

uint64_t AnonFixpoint::sum_to(uint64_t n) {
  {
    uint64_t _lc1_m = n;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    uint64_t _lc1_loop_m = _lc1_m;
    while (true) {
      if (_lc1_loop_m <= 0) {
        return _lc1_loop_acc;
      } else {
        uint64_t p = _lc1_loop_m - 1;
        uint64_t _next_m = p;
        _lc1_loop_acc = (_lc1_loop_m + _lc1_loop_acc);
        _lc1_loop_m = _next_m;
      }
    }
  }
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
  {
    uint64_t _lc1_fuel = (a + b);
    uint64_t _lc1_x = a;
    uint64_t _lc1_y = b;
    uint64_t _lc1_loop_y = _lc1_y;
    uint64_t _lc1_loop_x = _lc1_x;
    uint64_t _lc1_loop_fuel = _lc1_fuel;
    while (true) {
      if (_lc1_loop_fuel <= 0) {
        return _lc1_loop_x;
      } else {
        uint64_t f = _lc1_loop_fuel - 1;
        if (_lc1_loop_y <= 0) {
          return _lc1_loop_x;
        } else {
          uint64_t _x = _lc1_loop_y - 1;
          uint64_t _next_y =
              (_lc1_loop_y ? _lc1_loop_x % _lc1_loop_y : _lc1_loop_x);
          uint64_t _next_x = _lc1_loop_y;
          _lc1_loop_fuel = f;
          _lc1_loop_y = _next_y;
          _lc1_loop_x = _next_x;
        }
      }
    }
  }
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
  {
    uint64_t _lc1_n0 = foo;
    return foo0_impl(foo0_impl, _lc1_n0);
  }
}
