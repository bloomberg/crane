#include <disassemble_ops.h>

DisassembleOps::instruction DisassembleOps::decode1(const unsigned int &b1,
                                                    const unsigned int &b2) {
  if ((2u ? b1 % 2u : b1) == 0u) {
    return instruction::nop2();
  } else {
    return instruction::ldm2((16u ? b2 % 16u : b2));
  }
}

List<unsigned int> DisassembleOps::drop_(const unsigned int &n,
                                         List<unsigned int> l) {
  if (n <= 0) {
    return l;
  } else {
    unsigned int n_ = n - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v_mut())) {
      return List<unsigned int>::nil();
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v_mut());
      return drop_(n_, *(d_a1));
    }
  }
}

std::optional<std::pair<DisassembleOps::instruction, unsigned int>>
DisassembleOps::disassemble1(const List<unsigned int> &rom0,
                             const unsigned int &addr) {
  auto &&_sv = drop_(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return std::optional<
        std::pair<DisassembleOps::instruction, unsigned int>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return std::optional<
          std::pair<DisassembleOps::instruction, unsigned int>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, unsigned int>>(
          std::make_pair(decode1(d_a0, d_a00), (addr + 2u)));
    }
  }
}

DisassembleOps::instruction DisassembleOps::decode2(const unsigned int &b1,
                                                    const unsigned int &b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

std::optional<std::pair<DisassembleOps::instruction, unsigned int>>
DisassembleOps::disassemble2(const List<unsigned int> &rom0,
                             const unsigned int &addr) {
  auto &&_sv = drop<unsigned int>(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return std::optional<
        std::pair<DisassembleOps::instruction, unsigned int>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return std::optional<
          std::pair<DisassembleOps::instruction, unsigned int>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, unsigned int>>(
          std::make_pair(decode2(d_a0, d_a00), (addr + 2u)));
    }
  }
}

DisassembleOps::instruction DisassembleOps::decode3(const unsigned int &b1,
                                                    const unsigned int &b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

std::optional<std::pair<DisassembleOps::instruction, unsigned int>>
DisassembleOps::disassemble3(const List<unsigned int> &rom0,
                             const unsigned int &addr) {
  auto &&_sv = drop<unsigned int>(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return std::optional<
        std::pair<DisassembleOps::instruction, unsigned int>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return std::optional<
          std::pair<DisassembleOps::instruction, unsigned int>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, unsigned int>>(
          std::make_pair(decode3(d_a0, d_a00), (addr + 2u)));
    }
  }
}

DisassembleOps::instruction DisassembleOps::decode4(const unsigned int &b1,
                                                    const unsigned int &b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

std::optional<std::pair<DisassembleOps::instruction, unsigned int>>
DisassembleOps::disassemble4(const List<unsigned int> &rom0,
                             const unsigned int &addr) {
  auto &&_sv = drop<unsigned int>(addr, rom0);
  if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv.v())) {
    return std::optional<
        std::pair<DisassembleOps::instruction, unsigned int>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(_sv.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return std::optional<
          std::pair<DisassembleOps::instruction, unsigned int>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, unsigned int>>(
          std::make_pair(decode4(d_a0, d_a00), (addr + 2u)));
    }
  }
}
