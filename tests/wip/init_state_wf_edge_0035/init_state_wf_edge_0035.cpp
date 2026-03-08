#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <init_state_wf_edge_0035.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int InitStateWfEdge0035::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int InitStateWfEdge0035::pc_inc1(
    const std::shared_ptr<InitStateWfEdge0035::state> &s) {
  return addr12_of_nat((s->pc + 1u));
}

unsigned int InitStateWfEdge0035::page_of(const unsigned int p) {
  return Nat::div(p, 256u);
}

unsigned int InitStateWfEdge0035::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

unsigned int InitStateWfEdge0035::base_for_next1(
    const std::shared_ptr<InitStateWfEdge0035::state> &s) {
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
