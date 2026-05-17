#include "cpu_emulator.h"

uint64_t CpuEmulator::get_reg(const CpuEmulator::state &s, uint64_t r) {
  return ListDef::template nth<uint64_t>(r, s.ex_regs, UINT64_C(0));
}

List<uint64_t> CpuEmulator::set_reg(const CpuEmulator::state &s, uint64_t r,
                                    uint64_t v) {
  return update_nth<uint64_t>(r, (UINT64_C(16) ? v % UINT64_C(16) : v),
                              s.ex_regs);
}

uint64_t CpuEmulator::pair_base(uint64_t r) {
  return (((r - (UINT64_C(2) ? r % UINT64_C(2) : r)) > r
               ? 0
               : (r - (UINT64_C(2) ? r % UINT64_C(2) : r))));
}

uint64_t CpuEmulator::get_pair(const CpuEmulator::state &s, uint64_t r) {
  uint64_t base = pair_base(r);
  return (((UINT64_C(16) ? get_reg(s, base) % UINT64_C(16) : get_reg(s, base)) *
           UINT64_C(16)) +
          (UINT64_C(16) ? get_reg(s, (base + 1)) % UINT64_C(16)
                        : get_reg(s, (base + 1))));
}

List<uint64_t> CpuEmulator::set_pair(const CpuEmulator::state &s, uint64_t r,
                                     uint64_t v) {
  uint64_t base = pair_base(r);
  uint64_t hi =
      (UINT64_C(16) ? (UINT64_C(16) ? v / UINT64_C(16) : 0) % UINT64_C(16)
                    : (UINT64_C(16) ? v / UINT64_C(16) : 0));
  uint64_t lo = (UINT64_C(16) ? v % UINT64_C(16) : v);
  return update_nth<uint64_t>((base + 1), lo,
                              update_nth<uint64_t>(base, hi, s.ex_regs));
}

List<uint64_t> CpuEmulator::push_return(const CpuEmulator::state &s,
                                        uint64_t ret) {
  return List<uint64_t>::cons((UINT64_C(4096) ? ret % UINT64_C(4096) : ret),
                              s.ex_stack)
      .firstn(UINT64_C(2));
}

CpuEmulator::state CpuEmulator::execute(const CpuEmulator::state &s,
                                        const CpuEmulator::instr &i) {
  if (std::holds_alternative<typename CpuEmulator::instr::NOP>(i.v())) {
    return state{s.ex_acc,
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::LDM>(i.v())) {
    const auto &[n0] = std::get<typename CpuEmulator::instr::LDM>(i.v());
    return state{(UINT64_C(16) ? n0 % UINT64_C(16) : n0),
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::LD>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::LD>(i.v());
    return state{get_reg(s, r0),
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::XCH>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::XCH>(i.v());
    uint64_t regv = get_reg(s, r0);
    return state{regv,
                 set_reg(s, r0, s.ex_acc),
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::INC>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::INC>(i.v());
    return state{s.ex_acc,
                 set_reg(s, r0, (get_reg(s, r0) + 1)),
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::ADD>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::ADD>(i.v());
    uint64_t sum = ((s.ex_acc + get_reg(s, r0)) +
                    (s.ex_carry ? UINT64_C(1) : UINT64_C(0)));
    return state{(UINT64_C(16) ? sum % UINT64_C(16) : sum),
                 s.ex_regs,
                 UINT64_C(16) <= sum,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::SUB>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::SUB>(i.v());
    uint64_t diff = ((((s.ex_acc + UINT64_C(16)) - get_reg(s, r0)) >
                              (s.ex_acc + UINT64_C(16))
                          ? 0
                          : ((s.ex_acc + UINT64_C(16)) - get_reg(s, r0))));
    return state{(UINT64_C(16) ? diff % UINT64_C(16) : diff),
                 s.ex_regs,
                 get_reg(s, r0) <= s.ex_acc,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::IAC>(i.v())) {
    return state{
        (UINT64_C(16) ? (s.ex_acc + 1) % UINT64_C(16) : (s.ex_acc + 1)),
        s.ex_regs,
        UINT64_C(16) <= (s.ex_acc + 1),
        (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                        : (s.ex_pc + UINT64_C(1))),
        s.ex_stack,
        s.ex_pair_bus,
        s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::DAC>(i.v())) {
    return state{(UINT64_C(16) ? (s.ex_acc + UINT64_C(15)) % UINT64_C(16)
                               : (s.ex_acc + UINT64_C(15))),
                 s.ex_regs,
                 !(s.ex_acc == UINT64_C(0)),
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::CLC>(i.v())) {
    return state{s.ex_acc,
                 s.ex_regs,
                 false,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::STC>(i.v())) {
    return state{s.ex_acc,
                 s.ex_regs,
                 true,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::CMC>(i.v())) {
    return state{s.ex_acc,
                 s.ex_regs,
                 !(s.ex_carry),
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::CMA>(i.v())) {
    return state{(((UINT64_C(15) - s.ex_acc) > UINT64_C(15)
                       ? 0
                       : (UINT64_C(15) - s.ex_acc))),
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::CLB>(i.v())) {
    return state{UINT64_C(0),
                 s.ex_regs,
                 false,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::RAL>(i.v())) {
    uint64_t acc_ = (UINT64_C(16) ? ((UINT64_C(2) * s.ex_acc) +
                                     (s.ex_carry ? UINT64_C(1) : UINT64_C(0))) %
                                        UINT64_C(16)
                                  : ((UINT64_C(2) * s.ex_acc) +
                                     (s.ex_carry ? UINT64_C(1) : UINT64_C(0))));
    bool carry_ = UINT64_C(16) <= ((UINT64_C(2) * s.ex_acc) +
                                   (s.ex_carry ? UINT64_C(1) : UINT64_C(0)));
    return state{acc_,
                 s.ex_regs,
                 carry_,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::RAR>(i.v())) {
    uint64_t carry_bit;
    if (s.ex_carry) {
      carry_bit = UINT64_C(8);
    } else {
      carry_bit = UINT64_C(0);
    }
    return state{((UINT64_C(2) ? s.ex_acc / UINT64_C(2) : 0) + carry_bit),
                 s.ex_regs,
                 (UINT64_C(2) ? s.ex_acc % UINT64_C(2) : s.ex_acc) ==
                     UINT64_C(1),
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::TCC>(i.v())) {
    return state{(s.ex_carry ? UINT64_C(1) : UINT64_C(0)),
                 s.ex_regs,
                 false,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::TCS>(i.v())) {
    return state{(s.ex_carry ? UINT64_C(10) : UINT64_C(9)),
                 s.ex_regs,
                 false,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::DAA>(i.v())) {
    uint64_t acc_;
    if (UINT64_C(10) <= (s.ex_acc + 1)) {
      acc_ = (UINT64_C(16) ? (s.ex_acc + UINT64_C(6)) % UINT64_C(16)
                           : (s.ex_acc + UINT64_C(6)));
    } else {
      acc_ = s.ex_acc;
    }
    return state{acc_,
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::KBP>(i.v())) {
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
    return state{out,
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::JUN>(i.v())) {
    const auto &[a0] = std::get<typename CpuEmulator::instr::JUN>(i.v());
    return state{s.ex_acc,   s.ex_regs,
                 s.ex_carry, (UINT64_C(4096) ? a0 % UINT64_C(4096) : a0),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::JMS>(i.v())) {
    const auto &[a0] = std::get<typename CpuEmulator::instr::JMS>(i.v());
    return state{s.ex_acc,
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? a0 % UINT64_C(4096) : a0),
                 push_return(s, (s.ex_pc + UINT64_C(2))),
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::JCN>(i.v())) {
    const auto &[c0, a0] = std::get<typename CpuEmulator::instr::JCN>(i.v());
    bool jump =
        ((UINT64_C(2) ? c0 % UINT64_C(2) : c0) == UINT64_C(1) && s.ex_carry);
    return state{
        s.ex_acc,
        s.ex_regs,
        s.ex_carry,
        (jump ? (UINT64_C(4096) ? a0 % UINT64_C(4096) : a0)
              : (UINT64_C(4096) ? (s.ex_pc + UINT64_C(2)) % UINT64_C(4096)
                                : (s.ex_pc + UINT64_C(2)))),
        s.ex_stack,
        s.ex_pair_bus,
        s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::FIM>(i.v())) {
    const auto &[r0, d0] = std::get<typename CpuEmulator::instr::FIM>(i.v());
    return state{s.ex_acc,
                 set_pair(s, r0, d0),
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(2)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(2))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::SRC>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::SRC>(i.v());
    return state{s.ex_acc,
                 s.ex_regs,
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 get_pair(s, r0),
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::FIN>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::FIN>(i.v());
    return state{s.ex_acc,
                 set_pair(s, r0, s.ex_pair_bus),
                 s.ex_carry,
                 (UINT64_C(4096) ? (s.ex_pc + UINT64_C(1)) % UINT64_C(4096)
                                 : (s.ex_pc + UINT64_C(1))),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::JIN>(i.v())) {
    const auto &[r0] = std::get<typename CpuEmulator::instr::JIN>(i.v());
    return state{
        s.ex_acc,
        s.ex_regs,
        s.ex_carry,
        (UINT64_C(4096) ? get_pair(s, r0) % UINT64_C(4096) : get_pair(s, r0)),
        s.ex_stack,
        s.ex_pair_bus,
        s.ex_ports};
  } else if (std::holds_alternative<typename CpuEmulator::instr::ISZ>(i.v())) {
    const auto &[r0, a0] = std::get<typename CpuEmulator::instr::ISZ>(i.v());
    uint64_t n = (UINT64_C(16) ? (get_reg(s, r0) + 1) % UINT64_C(16)
                               : (get_reg(s, r0) + 1));
    return state{
        s.ex_acc,
        set_reg(s, r0, n),
        s.ex_carry,
        (n == UINT64_C(0)
             ? (UINT64_C(4096) ? a0 % UINT64_C(4096) : a0)
             : (UINT64_C(4096) ? (s.ex_pc + UINT64_C(2)) % UINT64_C(4096)
                               : (s.ex_pc + UINT64_C(2)))),
        s.ex_stack,
        s.ex_pair_bus,
        s.ex_ports};
  } else {
    const auto &[d0] = std::get<typename CpuEmulator::instr::BBL>(i.v());
    return state{
        (UINT64_C(16) ? d0 % UINT64_C(16) : d0),
        s.ex_regs,
        s.ex_carry,
        ListDef::template nth<uint64_t>(UINT64_C(0), s.ex_stack, UINT64_C(0)),
        s.ex_stack.skipn(UINT64_C(1)),
        s.ex_pair_bus,
        s.ex_ports};
  }
}
