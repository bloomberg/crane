#include <disassemble_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode1(const unsigned int b1, const unsigned int b2) {
  if ((b1 % 2u) == 0u) {
    return instruction::nop2();
  } else {
    return instruction::ldm2((std::move(b2) % 16u));
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
                     return List<unsigned int>::nil();
                   },
                   [&](const typename List<unsigned int>::Cons _args)
                       -> std::shared_ptr<List<unsigned int>> {
                     return drop_(std::move(n_), _args.d_a1);
                   }},
        l->v());
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble1(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::optional<std::pair<
                std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>();
                           },
                           [&](const typename List<unsigned int>::Cons _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode1(_args.d_a0, _args0.d_a0),
                                     (std::move(addr) + 2u)));
                           }},
                _args.d_a1->v());
          }},
      drop_(addr, rom0)->v());
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode2(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((std::move(b2) % 16u));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble2(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::optional<std::pair<
                std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>();
                           },
                           [&](const typename List<unsigned int>::Cons _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode2(_args.d_a0, _args0.d_a0),
                                     (std::move(addr) + 2u)));
                           }},
                _args.d_a1->v());
          }},
      drop<unsigned int>(addr, rom0)->v());
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode3(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((std::move(b2) % 16u));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble3(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::optional<std::pair<
                std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>();
                           },
                           [&](const typename List<unsigned int>::Cons _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode3(_args.d_a0, _args0.d_a0),
                                     (std::move(addr) + 2u)));
                           }},
                _args.d_a1->v());
          }},
      drop<unsigned int>(addr, rom0)->v());
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode4(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((std::move(b2) % 16u));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble4(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::optional<std::pair<
                std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
          },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::optional<std::pair<
                  std::shared_ptr<DisassembleOps::instruction>, unsigned int>> {
            return std::visit(
                Overloaded{[](const typename List<unsigned int>::Nil _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>();
                           },
                           [&](const typename List<unsigned int>::Cons _args0)
                               -> std::optional<std::pair<
                                   std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>> {
                             return std::make_optional<std::pair<
                                 std::shared_ptr<DisassembleOps::instruction>,
                                 unsigned int>>(
                                 std::make_pair(
                                     decode4(_args.d_a0, _args0.d_a0),
                                     (std::move(addr) + 2u)));
                           }},
                _args.d_a1->v());
          }},
      drop<unsigned int>(addr, rom0)->v());
}
