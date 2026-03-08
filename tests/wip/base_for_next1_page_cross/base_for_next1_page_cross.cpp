#include <algorithm>
#include <any>
#include <base_for_next1_page_cross.h>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int BaseForNext1PageCross::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int BaseForNext1PageCross::pc_inc1(
    const std::shared_ptr<BaseForNext1PageCross::state> &s) {
  return addr12_of_nat((s->pc + 1u));
}

unsigned int BaseForNext1PageCross::page_of(const unsigned int p) {
  return Nat::div(p, 256u);
}

unsigned int BaseForNext1PageCross::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

unsigned int BaseForNext1PageCross::base_for_next1(
    const std::shared_ptr<BaseForNext1PageCross::state> &s) {
  return page_base(pc_inc1(s));
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
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
