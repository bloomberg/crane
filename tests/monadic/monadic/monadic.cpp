#include <monadic.h>

#include <algorithm>
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

__attribute__((pure)) std::optional<unsigned int>
Monadic::safe_div(const unsigned int n, const unsigned int m) {
  if (m <= 0) {
    return std::nullopt;
  } else {
    unsigned int m_ = m - 1;
    return std::make_optional<unsigned int>(Nat::div(n, (m_ + 1)));
  }
}

__attribute__((pure)) std::optional<unsigned int>
Monadic::safe_sub(const unsigned int n, const unsigned int m) {
  if (n < m) {
    return std::nullopt;
  } else {
    return std::make_optional<unsigned int>(
        (((std::move(n) - std::move(m)) > std::move(n)
              ? 0
              : (std::move(n) - std::move(m)))));
  }
}

__attribute__((pure)) std::optional<unsigned int>
Monadic::div_then_sub(const unsigned int a, const unsigned int b,
                      const unsigned int c) {
  return option_bind<unsigned int, unsigned int>(
      safe_div(a, b), [=](unsigned int x) mutable {
        return option_bind<unsigned int, unsigned int>(
            safe_sub(x, c), option_return<unsigned int>);
      });
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
