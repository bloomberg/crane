#include <algorithm>
#include <any>
#include <cassert>
#include <disassemble_next_address.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<DisassembleNextAddress::instruction>
DisassembleNextAddress::decode(const unsigned int b1, const unsigned int b2) {
  if ((b1 == 0)) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_(
        (std::move(b2) %
         ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1)));
  }
}

std::optional<std::pair<std::shared_ptr<DisassembleNextAddress::instruction>,
                        unsigned int>>
DisassembleNextAddress::disassemble(
    const std::shared_ptr<List<unsigned int>> &rom, const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleNextAddress::instruction>,
                  unsigned int>> { return std::nullopt; },
          [&](const typename List<unsigned int>::cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleNextAddress::instruction>,
                  unsigned int>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<
                                          DisassembleNextAddress::instruction>,
                                      unsigned int>> { return std::nullopt; },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::optional<
                            std::pair<std::shared_ptr<
                                          DisassembleNextAddress::instruction>,
                                      unsigned int>> {
                      unsigned int b2 = _args._a0;
                      return std::make_optional<std::pair<
                          std::shared_ptr<DisassembleNextAddress::instruction>,
                          unsigned int>>(
                          std::make_pair(decode(std::move(b1), std::move(b2)),
                                         (std::move(addr) + ((0 + 1) + 1))));
                    }},
                std::move(l)->v());
          }},
      drop<unsigned int>(addr, rom)->v());
}
