#include <disassemble_ops.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode1(const unsigned int b1, const unsigned int b2) {
  if ((2u ? b1 % 2u : b1) == 0u) {
    return instruction::nop2();
  } else {
    return instruction::ldm2((16u ? b2 % 16u : b2));
  }
}

std::shared_ptr<List<unsigned int>>
DisassembleOps::drop_(const unsigned int n,
                      std::shared_ptr<List<unsigned int>> l) {
  if (n <= 0) {
    return l;
  } else {
    unsigned int n_ = n - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v()) &&
        l.use_count() == 1) {
      return l;
    } else if (std::holds_alternative<typename List<unsigned int>::Nil>(
                   l->v())) {
      return List<unsigned int>::nil();
    } else {
      const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&l->v());
      return drop_(n_, _m.d_a1);
    }
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble1(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  auto &&_sv = drop_(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::optional<std::pair<std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>>();
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      return std::make_optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>(
          std::make_pair(decode1(_m.d_a0, _m0.d_a0), (addr + 2u)));
    }
  }
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode2(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble2(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::optional<std::pair<std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>>();
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      return std::make_optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>(
          std::make_pair(decode2(_m.d_a0, _m0.d_a0), (addr + 2u)));
    }
  }
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode3(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble3(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::optional<std::pair<std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>>();
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      return std::make_optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>(
          std::make_pair(decode3(_m.d_a0, _m0.d_a0), (addr + 2u)));
    }
  }
}

std::shared_ptr<DisassembleOps::instruction>
DisassembleOps::decode4(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

__attribute__((pure)) std::optional<
    std::pair<std::shared_ptr<DisassembleOps::instruction>, unsigned int>>
DisassembleOps::disassemble4(const std::shared_ptr<List<unsigned int>> &rom0,
                             const unsigned int addr) {
  auto &&_sv = drop<unsigned int>(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv->v())) {
    return std::optional<std::pair<std::shared_ptr<DisassembleOps::instruction>,
                                   unsigned int>>();
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&_sv->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return std::optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>();
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      return std::make_optional<std::pair<
          std::shared_ptr<DisassembleOps::instruction>, unsigned int>>(
          std::make_pair(decode4(_m.d_a0, _m0.d_a0), (addr + 2u)));
    }
  }
}
