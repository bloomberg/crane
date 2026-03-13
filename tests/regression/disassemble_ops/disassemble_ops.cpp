#include <disassemble_ops.h>

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

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode1(const unsigned int b1, const unsigned int b2) {
  if ((b1 % 2u) == 0u) {
    return instruction::ctor::NOP2_();
  } else {
    return instruction::ctor::LDM2_((std::move(b2) % 16u));
  }
}

std::shared_ptr<List<unsigned int>>
DisassembleOps::drop_(const unsigned int n,
                      std::shared_ptr<List<unsigned int>> l) {
  if (n <= 0) {
    return std::move(l);
  } else {
    unsigned int n_ = n - 1;
    return std::visit(
        Overloaded{[](const typename List<unsigned int>::Nil _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     return List<unsigned int>::ctor::Nil_();
                   },
                   [&](const typename List<unsigned int>::Cons _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     std::shared_ptr<List<unsigned int>> l_ = _args.d_a1;
                     return drop_(std::move(n_), std::move(l_));
                   }},
        l->v());
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble1(const std::shared_ptr<List<unsigned int>> &rom,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            unsigned int b1 = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l = _args.d_a1;
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> { return std::nullopt; },
                           [&](const typename List<unsigned int>::Cons _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             unsigned int b2 = _args.d_a0;
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode1(std::move(b1), std::move(b2)),
                                     (std::move(addr) + 2u)));
                           }},
                std::move(l)->v());
          }},
      drop_(addr, rom)->v());
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode2(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble2(const std::shared_ptr<List<unsigned int>> &rom,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            unsigned int b1 = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l = _args.d_a1;
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> { return std::nullopt; },
                           [&](const typename List<unsigned int>::Cons _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             unsigned int b2 = _args.d_a0;
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode2(std::move(b1), std::move(b2)),
                                     (std::move(addr) + 2u)));
                           }},
                std::move(l)->v());
          }},
      drop<unsigned int>(addr, rom)->v());
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode3(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble3(const std::shared_ptr<List<unsigned int>> &rom,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            unsigned int b1 = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l = _args.d_a1;
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> { return std::nullopt; },
                           [&](const typename List<unsigned int>::Cons _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             unsigned int b2 = _args.d_a0;
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode3(std::move(b1), std::move(b2)),
                                     (std::move(addr) + 2u)));
                           }},
                std::move(l)->v());
          }},
      drop<unsigned int>(addr, rom)->v());
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode4(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::ctor::NOP_();
  } else {
    return instruction::ctor::LDM_((std::move(b2) % 16u));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble4(const std::shared_ptr<List<unsigned int>> &rom,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::nullopt;
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            unsigned int b1 = _args.d_a0;
            std::shared_ptr<List<unsigned int>> l = _args.d_a1;
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> { return std::nullopt; },
                           [&](const typename List<unsigned int>::Cons _args)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             unsigned int b2 = _args.d_a0;
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode4(std::move(b1), std::move(b2)),
                                     (std::move(addr) + 2u)));
                           }},
                std::move(l)->v());
          }},
      drop<unsigned int>(addr, rom)->v());
}
