#include <page_address.h>

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

__attribute__((pure)) unsigned int
PageAddress::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

__attribute__((pure)) unsigned int PageAddress::page_of(const unsigned int p) {
  return Nat::div(addr12_of_nat(p), 256u);
}

__attribute__((pure)) unsigned int
PageAddress::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

__attribute__((pure)) unsigned int
PageAddress::branch_target(const unsigned int pc, const unsigned int off) {
  return (page_base(addr12_of_nat((pc + 2u))) + (off % 256u));
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
