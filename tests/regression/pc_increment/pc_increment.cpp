#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <pc_increment.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int PcIncrement::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

unsigned int
PcIncrement::pc_inc1(const std::shared_ptr<PcIncrement::state> &s) {
  return addr12_of_nat((s->pc + 1u));
}

unsigned int
PcIncrement::pc_inc2(const std::shared_ptr<PcIncrement::state> &s) {
  return addr12_of_nat((s->pc + 2u));
}

std::shared_ptr<PcIncrement::instruction>
PcIncrement::decode(const unsigned int b1, const unsigned int b2) {
  if ((b1 == 0u)) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

std::optional<
    std::pair<std::shared_ptr<PcIncrement::instruction>, unsigned int>>
PcIncrement::disassemble(const std::shared_ptr<List<unsigned int>> &rom,
                         const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<PcIncrement::instruction>, unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<PcIncrement::instruction>, unsigned int>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<PcIncrement::instruction>,
                                      unsigned int>> { return std::nullopt; },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<PcIncrement::instruction>,
                                      unsigned int>> {
                      unsigned int b2 = _args._a0;
                      return std::make_optional<
                          std::pair<std::shared_ptr<PcIncrement::instruction>,
                                    unsigned int>>(
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
