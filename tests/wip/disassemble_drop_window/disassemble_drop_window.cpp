#include <algorithm>
#include <any>
#include <cassert>
#include <disassemble_drop_window.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<DisassembleDropWindow::instruction>
DisassembleDropWindow::decode(const unsigned int b1, const unsigned int b2) {
  if (((b1 % ((0 + 1) + 1)) == 0)) {
    return instruction::ctor::NOP__();
  } else {
    return instruction::ctor::LDM__(
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

std::shared_ptr<List<unsigned int>>
DisassembleDropWindow::drop_(const unsigned int n,
                             std::shared_ptr<List<unsigned int>> l) {
  if (n <= 0) {
    return std::move(l);
  } else {
    unsigned int n_ = n - 1;
    return std::visit(
        Overloaded{[](const typename List<unsigned int>::nil _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     return List<unsigned int>::ctor::nil_();
                   },
                   [&](const typename List<unsigned int>::cons _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     std::shared_ptr<List<unsigned int>> l_ = _args._a1;
                     return drop_(std::move(n_), std::move(l_));
                   }},
        l->v());
  }
}

std::optional<std::pair<std::shared_ptr<DisassembleDropWindow::instruction>,
                        unsigned int>>
DisassembleDropWindow::disassemble(
    const std::shared_ptr<List<unsigned int>> &rom, const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::nil _args)
              -> std::optional<
                  std::pair<std::shared_ptr<DisassembleDropWindow::instruction>,
                            unsigned int>> { return std::nullopt; },
          [&](const typename List<unsigned int>::cons _args)
              -> std::optional<
                  std::pair<std::shared_ptr<DisassembleDropWindow::instruction>,
                            unsigned int>> {
            unsigned int b1 = _args._a0;
            std::shared_ptr<List<unsigned int>> l = _args._a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::nil _args)
                        -> std::optional<std::pair<
                            std::shared_ptr<DisassembleDropWindow::instruction>,
                            unsigned int>> { return std::nullopt; },
                    [&](const typename List<unsigned int>::cons _args)
                        -> std::optional<std::pair<
                            std::shared_ptr<DisassembleDropWindow::instruction>,
                            unsigned int>> {
                      unsigned int b2 = _args._a0;
                      return std::make_optional<std::pair<
                          std::shared_ptr<DisassembleDropWindow::instruction>,
                          unsigned int>>(
                          std::make_pair(decode(std::move(b1), std::move(b2)),
                                         (std::move(addr) + ((0 + 1) + 1))));
                    }},
                std::move(l)->v());
          }},
      drop_(addr, rom)->v());
}
