#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <register_pair_even_rounding.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<List<unsigned int>> RegisterPairEvenRounding::regs_(
    const std::shared_ptr<RegisterPairEvenRounding::state> &s) {
  return s->regs_;
}

unsigned int RegisterPairEvenRounding::get_reg(
    const std::shared_ptr<RegisterPairEvenRounding::state> &s,
    const unsigned int r) {
  return s->regs_->nth(r, 0);
}

std::shared_ptr<RegisterPairEvenRounding::state>
RegisterPairEvenRounding::set_reg(
    std::shared_ptr<RegisterPairEvenRounding::state> s, const unsigned int r,
    const unsigned int v) {
  return std::make_shared<RegisterPairEvenRounding::state>(
      state{update_nth<unsigned int>(
          std::move(r),
          (std::move(v) %
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)),
          std::move(s)->regs_)});
}

unsigned int RegisterPairEvenRounding::get_reg_pair(
    const std::shared_ptr<RegisterPairEvenRounding::state> &s,
    const unsigned int r) {
  unsigned int r_even =
      (((r - (r % ((0 + 1) + 1))) > r ? 0 : (r - (r % ((0 + 1) + 1)))));
  unsigned int hi = get_reg(s, std::move(r_even));
  unsigned int lo = get_reg(s, (std::move(r_even) + (0 + 1)));
  return ((std::move(hi) *
           ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1)) +
          std::move(lo));
}

std::shared_ptr<RegisterPairEvenRounding::state>
RegisterPairEvenRounding::set_reg_pair(
    const std::shared_ptr<RegisterPairEvenRounding::state> &s,
    const unsigned int r, const unsigned int v) {
  unsigned int r_even =
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
  std::shared_ptr<RegisterPairEvenRounding::state> s1 =
      set_reg(s, std::move(r_even), std::move(hi));
  return set_reg(std::move(s1), (std::move(r_even) + (0 + 1)), std::move(lo));
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
