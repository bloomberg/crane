#include "disassemble_ops.h"

DisassembleOps::instruction DisassembleOps::decode1(uint64_t b1, uint64_t b2) {
  if ((UINT64_C(2) ? b1 % UINT64_C(2) : b1) == UINT64_C(0)) {
    return instruction::nop2();
  } else {
    return instruction::ldm2((UINT64_C(16) ? b2 % UINT64_C(16) : b2));
  }
}

List<uint64_t> DisassembleOps::drop_(uint64_t n, List<uint64_t> l) {
  if (n <= 0) {
    return l;
  } else {
    uint64_t n_ = n - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return List<uint64_t>::nil();
    } else {
      auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
      return drop_(n_, *a1);
    }
  }
}

std::optional<std::pair<DisassembleOps::instruction, uint64_t>>
DisassembleOps::disassemble1(const List<uint64_t> &rom0, uint64_t addr) {
  auto &&_sv = drop_(addr, rom0);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, uint64_t>>(
          std::make_pair(decode1(a0, a00), (addr + UINT64_C(2))));
    }
  }
}

DisassembleOps::instruction DisassembleOps::decode2(uint64_t b1, uint64_t b2) {
  if (b1 == UINT64_C(0)) {
    return instruction::nop();
  } else {
    return instruction::ldm((UINT64_C(16) ? b2 % UINT64_C(16) : b2));
  }
}

std::optional<std::pair<DisassembleOps::instruction, uint64_t>>
DisassembleOps::disassemble2(const List<uint64_t> &rom0, uint64_t addr) {
  auto &&_sv = drop<uint64_t>(addr, rom0);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, uint64_t>>(
          std::make_pair(decode2(a0, a00), (addr + UINT64_C(2))));
    }
  }
}

DisassembleOps::instruction DisassembleOps::decode3(uint64_t b1, uint64_t b2) {
  if (b1 == UINT64_C(0)) {
    return instruction::nop();
  } else {
    return instruction::ldm((UINT64_C(16) ? b2 % UINT64_C(16) : b2));
  }
}

std::optional<std::pair<DisassembleOps::instruction, uint64_t>>
DisassembleOps::disassemble3(const List<uint64_t> &rom0, uint64_t addr) {
  auto &&_sv = drop<uint64_t>(addr, rom0);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, uint64_t>>(
          std::make_pair(decode3(a0, a00), (addr + UINT64_C(2))));
    }
  }
}

DisassembleOps::instruction DisassembleOps::decode4(uint64_t b1, uint64_t b2) {
  if (b1 == UINT64_C(0)) {
    return instruction::nop();
  } else {
    return instruction::ldm((UINT64_C(16) ? b2 % UINT64_C(16) : b2));
  }
}

std::optional<std::pair<DisassembleOps::instruction, uint64_t>>
DisassembleOps::disassemble4(const List<uint64_t> &rom0, uint64_t addr) {
  auto &&_sv = drop<uint64_t>(addr, rom0);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::optional<std::pair<DisassembleOps::instruction, uint64_t>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return std::make_optional<
          std::pair<DisassembleOps::instruction, uint64_t>>(
          std::make_pair(decode4(a0, a00), (addr + UINT64_C(2))));
    }
  }
}
