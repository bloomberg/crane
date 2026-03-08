#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <pc_inc1_edge_0011.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<PcInc1Edge0011::instruction>
PcInc1Edge0011::decode(const unsigned int b1, const unsigned int b2) {
  if ((b1 == 0u)) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

std::optional<
    std::pair<std::shared_ptr<PcInc1Edge0011::instruction>, unsigned int>>
PcInc1Edge0011::disassemble(const std::shared_ptr<List<unsigned int>> &rom,
                            const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<PcInc1Edge0011::instruction>, unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<PcInc1Edge0011::instruction>, unsigned int>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::nil _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<PcInc1Edge0011::instruction>,
                                   unsigned int>> { return std::nullopt; },
                           [&](const typename List<unsigned int>::cons _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<PcInc1Edge0011::instruction>,
                                   unsigned int>> {
                             unsigned int b2 = _args._a0;
                             return std::make_optional<std::pair<
                                 std::shared_ptr<PcInc1Edge0011::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode(std::move(b1), std::move(b2)),
                                     (std::move(addr) + 2u)));
                           }},
                std::move(l)->v());
          }},
      drop<unsigned int>(addr, rom)->v());
}
