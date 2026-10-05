#include "get_pair_bound_prop.h"

uint64_t GetPairBoundProp::get_reg(const GetPairBoundProp::state &s,
                                   uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.ex_regs, UINT64_C(0));
}

List<uint64_t> GetPairBoundProp::set_reg(const GetPairBoundProp::state &s,
                                         uint64_t r, uint64_t v) {
  return update_nth<uint64_t>(r, (v % UINT64_C(16)), s.ex_regs);
}

uint64_t GetPairBoundProp::pair_base(uint64_t r) {
  auto &&_once1 = (r % UINT64_C(2));
  return (((r - _once1) > r ? 0 : (r - _once1)));
}

uint64_t GetPairBoundProp::get_pair(const GetPairBoundProp::state &s,
                                    uint64_t r) {
  uint64_t base = pair_base(r);
  auto &&_once1 = get_reg(s, (base + 1));
  auto &&_once2 = get_reg(s, base);
  return (((_once2 % UINT64_C(16)) * UINT64_C(16)) + (_once1 % UINT64_C(16)));
}

List<uint64_t> GetPairBoundProp::set_pair(const GetPairBoundProp::state &s,
                                          uint64_t r, uint64_t v) {
  uint64_t base = pair_base(r);
  auto &&_once1 = (v / UINT64_C(16));
  uint64_t hi = (_once1 % UINT64_C(16));
  uint64_t lo = (v % UINT64_C(16));
  return update_nth<uint64_t>((base + 1), lo,
                              update_nth<uint64_t>(base, hi, s.ex_regs));
}

List<uint64_t> GetPairBoundProp::push_return(const GetPairBoundProp::state &s,
                                             uint64_t ret) {
  return List<uint64_t>::cons((ret % UINT64_C(4096)), s.ex_stack)
      .firstn(UINT64_C(2));
}

GetPairBoundProp::state
GetPairBoundProp::execute(const GetPairBoundProp::state &s,
                          const GetPairBoundProp::instr &i) {
  if (std::holds_alternative<typename GetPairBoundProp::instr::NOP>(i.v())) {
    auto &&_once1 = (s.ex_pc + UINT64_C(1));
    return state{
        s.ex_acc,   s.ex_regs,     s.ex_carry, (_once1 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::LDM>(
                 i.v())) {
    const auto &[n0] = std::get<typename GetPairBoundProp::instr::LDM>(i.v());
    auto &&_once2 = (s.ex_pc + UINT64_C(1));
    return state{(n0 % UINT64_C(16)), s.ex_regs,
                 s.ex_carry,          (_once2 % UINT64_C(4096)),
                 s.ex_stack,          s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::LD>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::LD>(i.v());
    auto &&_once3 = (s.ex_pc + UINT64_C(1));
    return state{
        get_reg(s, r0), s.ex_regs,     s.ex_carry, (_once3 % UINT64_C(4096)),
        s.ex_stack,     s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::XCH>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::XCH>(i.v());
    uint64_t regv = get_reg(s, r0);
    auto &&_once4 = (s.ex_pc + UINT64_C(1));
    return state{regv,       set_reg(s, r0, s.ex_acc),
                 s.ex_carry, (_once4 % UINT64_C(4096)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::INC>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::INC>(i.v());
    auto &&_once5 = (s.ex_pc + UINT64_C(1));
    return state{s.ex_acc,   set_reg(s, r0, (get_reg(s, r0) + 1)),
                 s.ex_carry, (_once5 % UINT64_C(4096)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::ADD>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::ADD>(i.v());
    uint64_t sum = ((s.ex_acc + get_reg(s, r0)) +
                    (s.ex_carry ? UINT64_C(1) : UINT64_C(0)));
    auto &&_once6 = (s.ex_pc + UINT64_C(1));
    return state{(sum % UINT64_C(16)),
                 s.ex_regs,
                 UINT64_C(16) <= sum,
                 (_once6 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::SUB>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::SUB>(i.v());
    auto &&_once7 = (s.ex_acc + UINT64_C(16));
    auto &&_once8 = get_reg(s, r0);
    uint64_t diff = (((_once7 - _once8) > _once7 ? 0 : (_once7 - _once8)));
    auto &&_once9 = (s.ex_pc + UINT64_C(1));
    return state{(diff % UINT64_C(16)),
                 s.ex_regs,
                 get_reg(s, r0) <= s.ex_acc,
                 (_once9 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::IAC>(
                 i.v())) {
    auto &&_once10 = (s.ex_acc + 1);
    auto &&_once11 = (s.ex_pc + UINT64_C(1));
    return state{(_once10 % UINT64_C(16)),
                 s.ex_regs,
                 UINT64_C(16) <= (s.ex_acc + 1),
                 (_once11 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::DAC>(
                 i.v())) {
    auto &&_once12 = (s.ex_acc + UINT64_C(15));
    auto &&_once13 = (s.ex_pc + UINT64_C(1));
    return state{(_once12 % UINT64_C(16)),
                 s.ex_regs,
                 !(s.ex_acc == UINT64_C(0)),
                 (_once13 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CLC>(
                 i.v())) {
    auto &&_once14 = (s.ex_pc + UINT64_C(1));
    return state{
        s.ex_acc,   s.ex_regs,     false,     (_once14 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::STC>(
                 i.v())) {
    auto &&_once15 = (s.ex_pc + UINT64_C(1));
    return state{
        s.ex_acc,   s.ex_regs,     true,      (_once15 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CMC>(
                 i.v())) {
    auto &&_once16 = (s.ex_pc + UINT64_C(1));
    return state{
        s.ex_acc,   s.ex_regs,     !(s.ex_carry), (_once16 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CMA>(
                 i.v())) {
    auto &&_once17 = (s.ex_pc + UINT64_C(1));
    return state{(((UINT64_C(15) - s.ex_acc) > UINT64_C(15)
                       ? 0
                       : (UINT64_C(15) - s.ex_acc))),
                 s.ex_regs,
                 s.ex_carry,
                 (_once17 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CLB>(
                 i.v())) {
    auto &&_once18 = (s.ex_pc + UINT64_C(1));
    return state{
        UINT64_C(0), s.ex_regs,     false,     (_once18 % UINT64_C(4096)),
        s.ex_stack,  s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::RAL>(
                 i.v())) {
    auto &&_once19 =
        ((UINT64_C(2) * s.ex_acc) + (s.ex_carry ? UINT64_C(1) : UINT64_C(0)));
    uint64_t acc_ = (_once19 % UINT64_C(16));
    bool carry_ = UINT64_C(16) <= ((UINT64_C(2) * s.ex_acc) +
                                   (s.ex_carry ? UINT64_C(1) : UINT64_C(0)));
    auto &&_once20 = (s.ex_pc + UINT64_C(1));
    return state{
        acc_,       s.ex_regs,     carry_,    (_once20 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::RAR>(
                 i.v())) {
    uint64_t carry_bit;
    if (s.ex_carry) {
      carry_bit = UINT64_C(8);
    } else {
      carry_bit = UINT64_C(0);
    }
    auto &&_once21 = (s.ex_pc + UINT64_C(1));
    return state{((s.ex_acc / UINT64_C(2)) + carry_bit),
                 s.ex_regs,
                 (s.ex_acc % UINT64_C(2)) == UINT64_C(1),
                 (_once21 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::TCC>(
                 i.v())) {
    auto &&_once22 = (s.ex_pc + UINT64_C(1));
    return state{(s.ex_carry ? UINT64_C(1) : UINT64_C(0)),
                 s.ex_regs,
                 false,
                 (_once22 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::TCS>(
                 i.v())) {
    auto &&_once23 = (s.ex_pc + UINT64_C(1));
    return state{(s.ex_carry ? UINT64_C(10) : UINT64_C(9)),
                 s.ex_regs,
                 false,
                 (_once23 % UINT64_C(4096)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::DAA>(
                 i.v())) {
    uint64_t acc_;
    if (UINT64_C(10) <= (s.ex_acc + 1)) {
      auto &&_once24 = (s.ex_acc + UINT64_C(6));
      acc_ = (_once24 % UINT64_C(16));
    } else {
      acc_ = s.ex_acc;
    }
    auto &&_once25 = (s.ex_pc + UINT64_C(1));
    return state{
        acc_,       s.ex_regs,     s.ex_carry, (_once25 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::KBP>(
                 i.v())) {
    uint64_t a = s.ex_acc;
    uint64_t out;
    if (a == UINT64_C(0)) {
      out = UINT64_C(0);
    } else {
      if (a == UINT64_C(1)) {
        out = UINT64_C(0);
      } else {
        if (a == UINT64_C(2)) {
          out = UINT64_C(1);
        } else {
          if (a == UINT64_C(4)) {
            out = UINT64_C(2);
          } else {
            if (a == UINT64_C(8)) {
              out = UINT64_C(3);
            } else {
              out = UINT64_C(15);
            }
          }
        }
      }
    }
    auto &&_once26 = (s.ex_pc + UINT64_C(1));
    return state{
        out,        s.ex_regs,     s.ex_carry, (_once26 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JUN>(
                 i.v())) {
    const auto &[a0] = std::get<typename GetPairBoundProp::instr::JUN>(i.v());
    return state{s.ex_acc,   s.ex_regs,     s.ex_carry, (a0 % UINT64_C(4096)),
                 s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JMS>(
                 i.v())) {
    const auto &[a0] = std::get<typename GetPairBoundProp::instr::JMS>(i.v());
    return state{s.ex_acc,
                 s.ex_regs,
                 s.ex_carry,
                 (a0 % UINT64_C(4096)),
                 push_return(s, (s.ex_pc + UINT64_C(2))),
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JCN>(
                 i.v())) {
    const auto &[c0, a0] =
        std::get<typename GetPairBoundProp::instr::JCN>(i.v());
    bool jump = ((c0 % UINT64_C(2)) == UINT64_C(1) && s.ex_carry);
    return state{s.ex_acc,
                 s.ex_regs,
                 s.ex_carry,
                 [&]() -> uint64_t {
                   if (jump) {
                     return (a0 % UINT64_C(4096));
                   } else {
                     auto &&_once27 = (s.ex_pc + UINT64_C(2));
                     return (_once27 % UINT64_C(4096));
                   }
                 }(),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::FIM>(
                 i.v())) {
    const auto &[r0, d0] =
        std::get<typename GetPairBoundProp::instr::FIM>(i.v());
    auto &&_once28 = (s.ex_pc + UINT64_C(2));
    return state{
        s.ex_acc,   set_pair(s, r0, d0), s.ex_carry, (_once28 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus,       s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::SRC>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::SRC>(i.v());
    auto &&_once29 = (s.ex_pc + UINT64_C(1));
    return state{
        s.ex_acc,   s.ex_regs,       s.ex_carry, (_once29 % UINT64_C(4096)),
        s.ex_stack, get_pair(s, r0), s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::FIN>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::FIN>(i.v());
    auto &&_once30 = (s.ex_pc + UINT64_C(1));
    return state{s.ex_acc,   set_pair(s, r0, s.ex_pair_bus),
                 s.ex_carry, (_once30 % UINT64_C(4096)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JIN>(
                 i.v())) {
    const auto &[r0] = std::get<typename GetPairBoundProp::instr::JIN>(i.v());
    auto &&_once31 = get_pair(s, r0);
    return state{
        s.ex_acc,   s.ex_regs,     s.ex_carry, (_once31 % UINT64_C(4096)),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::ISZ>(
                 i.v())) {
    const auto &[r0, a0] =
        std::get<typename GetPairBoundProp::instr::ISZ>(i.v());
    auto &&_once32 = (get_reg(s, r0) + 1);
    uint64_t n = (_once32 % UINT64_C(16));
    return state{s.ex_acc,
                 set_reg(s, r0, n),
                 s.ex_carry,
                 [&]() -> uint64_t {
                   if (n == UINT64_C(0)) {
                     return (a0 % UINT64_C(4096));
                   } else {
                     auto &&_once33 = (s.ex_pc + UINT64_C(2));
                     return (_once33 % UINT64_C(4096));
                   }
                 }(),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else {
    const auto &[d0] = std::get<typename GetPairBoundProp::instr::BBL>(i.v());
    return state{
        (d0 % UINT64_C(16)),
        s.ex_regs,
        s.ex_carry,
        ListDef::template nth<uint64_t>(UINT64_C(0), s.ex_stack, UINT64_C(0)),
        s.ex_stack.skipn(UINT64_C(1)),
        s.ex_pair_bus,
        s.ex_ports};
  }
}
