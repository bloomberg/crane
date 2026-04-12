#include <page_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
PageOps::addr12_of_nat(const unsigned int n) {
  return (4096u ? n % 4096u : n);
}

__attribute__((pure)) unsigned int PageOps::page_of(const unsigned int p) {
  return (256u ? p / 256u : 0);
}

__attribute__((pure)) unsigned int PageOps::page_base(const unsigned int p) {
  return (page_of(p) * 256u);
}

__attribute__((pure)) unsigned int PageOps::page_offset(const unsigned int p) {
  return (256u ? p % 256u : p);
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
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

__attribute__((pure))
std::optional<std::pair<std::shared_ptr<PageOps::instruction>, unsigned int>>
PageOps::disassemble(const std::shared_ptr<List<unsigned int>> &rom,
                     const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil &)
              -> std::optional<std::pair<std::shared_ptr<PageOps::instruction>,
                                         unsigned int>> {
            return std::optional<std::pair<
                std::shared_ptr<PageOps::instruction>, unsigned int>>();
          },
          [&](const typename List<unsigned int>::Cons &_args)
              -> std::optional<std::pair<std::shared_ptr<PageOps::instruction>,
                                         unsigned int>> {
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil &)
                        -> std::optional<
                            std::pair<std::shared_ptr<PageOps::instruction>,
                                      unsigned int>> {
                      return std::optional<
                          std::pair<std::shared_ptr<PageOps::instruction>,
                                    unsigned int>>();
                    },
                    [&](const typename List<unsigned int>::Cons &_args0)
                        -> std::optional<
                            std::pair<std::shared_ptr<PageOps::instruction>,
                                      unsigned int>> {
                      return std::make_optional<std::pair<
                          std::shared_ptr<PageOps::instruction>, unsigned int>>(
                          std::make_pair(decode(_args.d_a0, _args0.d_a0),
                                         (addr + 2u)));
                    }},
                _args.d_a1->v());
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
