#include <page_ops.h>

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
PageOps::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

__attribute__((pure)) unsigned int PageOps::page_of(const unsigned int p) {
  return Nat::div(p, 256u);
}

__attribute__((pure)) unsigned int PageOps::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

__attribute__((pure)) unsigned int PageOps::page_offset(const unsigned int p) {
  return (p % 256u);
}

__attribute__((pure)) unsigned int
PageOps::pc_inc1(const std::shared_ptr<PageOps::state> &s) {
  return addr12_of_nat((s->pc + 1u));
}

__attribute__((pure)) unsigned int
PageOps::pc_inc2(const std::shared_ptr<PageOps::state> &s) {
  return addr12_of_nat((s->pc + 2u));
}

__attribute__((pure)) unsigned int
PageOps::base_for_next1(const std::shared_ptr<PageOps::state> &s) {
  return page_base(pc_inc1(s));
}

__attribute__((pure)) unsigned int
PageOps::base_for_next2(const std::shared_ptr<PageOps::state> &s) {
  return page_base(pc_inc2(s));
}

__attribute__((pure)) unsigned int PageOps::recompose(const unsigned int p) {
  return (page_base(p) + page_offset(p));
}

std::shared_ptr<PageOps::instruction> PageOps::decode(const unsigned int b1,
                                                      const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<PageOps::instruction>, unsigned int>>
PageOps::disassemble(const std::shared_ptr<List<unsigned int>> &rom,
                     const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<std::shared_ptr<PageOps::instruction>,
                                         unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<std::shared_ptr<PageOps::instruction>,
                                         unsigned int>> {
            unsigned int b1 = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l = _args.d_a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<PageOps::instruction>,
                                      unsigned int>> { return std::nullopt; },
                    [&](const typename List<unsigned int>::Cons _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<PageOps::instruction>,
                                      unsigned int>> {
                      unsigned int b2 = _args.d_a0;
                      return std::make_optional<std::pair<
                          std::shared_ptr<PageOps::instruction>, unsigned int>>(
                          std::make_pair(decode(std::move(b1), std::move(b2)),
                                         (std::move(addr) + 2u)));
                    }},
                std::move(l)->v());
          }},
      drop<unsigned int>(addr, rom)->v());
}

__attribute__((pure)) unsigned int Nat::pow(const unsigned int n,
                                            const unsigned int m) {
  if (m <= 0) {
    return 1u;
  } else {
    unsigned int m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
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
