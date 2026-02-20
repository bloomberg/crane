#include <algorithm>
#include <anon_fixpoint.h>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int AnonFixpoint::sum_to(const unsigned int n) {
  std::function<unsigned int(unsigned int, unsigned int)> go;
  go = [&](unsigned int m, unsigned int acc) -> unsigned int {
    if (m <= 0) {
      return std::move(acc);
    } else {
      unsigned int p = m - 1;
      return go(std::move(p), (m + acc));
    }
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
    std::function<unsigned int(unsigned int)> inner;
    inner = [&](unsigned int k) -> unsigned int {
      if (k <= 0) {
        return 0u;
      } else {
        unsigned int q = k - 1;
        return (1u + inner(q));
      }
    };
    return (inner(m) + double_sum(p));
  }
}

unsigned int AnonFixpoint::gcd(const unsigned int a, const unsigned int b) {
  std::function<unsigned int(unsigned int, unsigned int, unsigned int)> go;
  go = [&](unsigned int fuel, unsigned int x, unsigned int y) -> unsigned int {
    if (fuel <= 0) {
      return std::move(x);
    } else {
      unsigned int f = fuel - 1;
      if (y <= 0) {
        return x;
      } else {
        unsigned int _x = y - 1;
        return go(std::move(f), y, (x % y));
      }
    }
  };
  return go((a + b), a, b);
}

unsigned int AnonFixpoint::test_shadow(const unsigned int n) {
  unsigned int foo = (n + n);
  std::function<unsigned int(unsigned int)> foo0;
  foo0 = [&](unsigned int n0) -> unsigned int {
    if (n0 <= 0) {
      return 0;
    } else {
      unsigned int n_ = n0 - 1;
      return (foo0(n_) + 1);
    }
  };
  return foo0(foo);
}
