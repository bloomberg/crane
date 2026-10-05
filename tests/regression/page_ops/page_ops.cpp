#include "page_ops.h"

uint64_t PageOps::addr12_of_nat(uint64_t n) {
  return (UINT64_C(4096) ? n % UINT64_C(4096) : n);
}

uint64_t PageOps::page_of(uint64_t p) {
  return (UINT64_C(256) ? p / UINT64_C(256) : 0);
}

uint64_t PageOps::page_base(uint64_t p) { return (page_of(p) * UINT64_C(256)); }

uint64_t PageOps::page_offset(uint64_t p) {
  return (UINT64_C(256) ? p % UINT64_C(256) : p);
}

uint64_t PageOps::pc_inc1(const PageOps::state &s) {
  return addr12_of_nat((s.pc + UINT64_C(1)));
}

uint64_t PageOps::pc_inc2(const PageOps::state &s) {
  return addr12_of_nat((s.pc + UINT64_C(2)));
}

uint64_t PageOps::base_for_next1(const PageOps::state &s) {
  return page_base(pc_inc1(s));
}

uint64_t PageOps::base_for_next2(const PageOps::state &s) {
  return page_base(pc_inc2(s));
}

uint64_t PageOps::recompose(uint64_t p) {
  return (page_base(p) + page_offset(p));
}

PageOps::instruction PageOps::decode(uint64_t b1, uint64_t b2) {
  if (b1 == UINT64_C(0)) {
    return instruction::nop();
  } else {
    return instruction::ldm((UINT64_C(16) ? b2 % UINT64_C(16) : b2));
  }
}

std::optional<std::pair<PageOps::instruction, uint64_t>>
PageOps::disassemble(const List<uint64_t> &rom, uint64_t addr) {
  auto &&_sv = drop<uint64_t>(addr, rom);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
    return std::optional<std::pair<PageOps::instruction, uint64_t>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(_sv.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return std::optional<std::pair<PageOps::instruction, uint64_t>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return std::make_optional<std::pair<PageOps::instruction, uint64_t>>(
          std::make_pair(decode(a0, a00), (addr + UINT64_C(2))));
    }
  }
}

uint64_t Nat::pow(uint64_t n, uint64_t m) {
  if (m <= 0) {
    return UINT64_C(1);
  } else {
    uint64_t m0 = m - 1;
    return (n * Nat::pow(n, m0));
  }
}
