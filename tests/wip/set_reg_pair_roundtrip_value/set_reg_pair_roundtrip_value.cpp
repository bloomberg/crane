#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_reg_pair_roundtrip_value.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> SetRegPairRoundtripValue::regs(
    const std::shared_ptr<SetRegPairRoundtripValue::state> &s) {
  return s->regs;
}

unsigned int SetRegPairRoundtripValue::get_reg(
    const std::shared_ptr<SetRegPairRoundtripValue::state> &s,
    const unsigned int r) {
  return s->regs->nth(r, 0);
}

std::shared_ptr<List<unsigned int>> SetRegPairRoundtripValue::update_nth_nat(
    const unsigned int n, const unsigned int x,
    std::shared_ptr<List<unsigned int>> l) {
  if ((n < l->length())) {
    return l->firstn(n)->app(
        List<unsigned int>::ctor::cons_(std::move(x), l->skipn((n + 1))));
  } else {
    return std::move(l);
  }
}

unsigned int SetRegPairRoundtripValue::get_reg_pair(
    const std::shared_ptr<SetRegPairRoundtripValue::state> &s,
    const unsigned int r) {
  unsigned int base =
      (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
  return ((get_reg(s, base) *
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)) +
          get_reg(s, (base + (0 + 1))));
}

std::shared_ptr<SetRegPairRoundtripValue::state>
SetRegPairRoundtripValue::set_reg_pair(
    std::shared_ptr<SetRegPairRoundtripValue::state> s, const unsigned int r,
    const unsigned int v) {
  unsigned int base =
      (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
  unsigned int hi = Nat::div(
      v,
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
  unsigned int lo =
      (v % ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1));
  return std::make_shared<SetRegPairRoundtripValue::state>(state{
      update_nth_nat((base + (0 + 1)), std::move(lo),
                     update_nth_nat(base, std::move(hi), std::move(s)->regs))});
}

std::pair<unsigned int, unsigned int> Nat::divmod(const unsigned int x,
                                                  const unsigned int y,
                                                  const unsigned int q,
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

unsigned int Nat::div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0, y_).first;
  }
}
