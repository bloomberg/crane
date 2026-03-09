#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <page_ops.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int PageOps::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int PageOps::page_of(const unsigned int p) {
  return Nat::div(p, 256u);
}

unsigned int PageOps::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

unsigned int PageOps::page_offset(const unsigned int p) { return (p % 256u); }

unsigned int PageOps::pc_inc1(const std::shared_ptr<PageOps::state> &s) {
  return addr12_of_nat((s->pc + 1u));
}

unsigned int PageOps::pc_inc2(const std::shared_ptr<PageOps::state> &s) {
  return addr12_of_nat((s->pc + 2u));
}

unsigned int PageOps::base_for_next1(const std::shared_ptr<PageOps::state> &s) {
  return page_base(pc_inc1(s));
}

unsigned int PageOps::base_for_next2(const std::shared_ptr<PageOps::state> &s) {
  return page_base(pc_inc2(s));
}

unsigned int PageOps::recompose(const unsigned int p) {
  return (page_base(p) + page_offset(p));
}

std::shared_ptr<PageOps::instruction> PageOps::decode(const unsigned int b1,
                                                      const unsigned int b2) {
  if ((b1 == 0u)) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

std::optional<std::pair<std::shared_ptr<PageOps::instruction>, unsigned int>>
PageOps::disassemble(const std::shared_ptr<List<unsigned int>> &rom,
                     const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::optional<std::pair<std::shared_ptr<PageOps::instruction>,
                                         unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::optional<std::pair<std::shared_ptr<PageOps::instruction>,
                                         unsigned int>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<PageOps::instruction>,
                                      unsigned int>> { return std::nullopt; },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<PageOps::instruction>,
                                      unsigned int>> {
                      unsigned int b2 = _args._a0;
                      return std::make_optional<std::pair<
                          std::shared_ptr<PageOps::instruction>, unsigned int>>(
                          std::make_pair(decode(std::move(b1), std::move(b2)),
                                         (std::move(addr) + 2u)));
                    }},
                std::move(l)->v());
          }},
      drop<unsigned int>(addr, rom)->v());
}

unsigned int Nat::pow(const unsigned int n, const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
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
