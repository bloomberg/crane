#include <get_pair_bound_prop.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
GetPairBoundProp::get_reg(const GetPairBoundProp::state &s,
                          const unsigned int &r) {
  return ListDef::template nth<unsigned int>(r, s.ex_regs, 0u);
}

__attribute__((pure)) List<unsigned int>
GetPairBoundProp::set_reg(const GetPairBoundProp::state &s,
                          const unsigned int &r, const unsigned int &v) {
  return update_nth<unsigned int>(r, (16u ? v % 16u : v), s.ex_regs);
}

__attribute__((pure)) unsigned int
GetPairBoundProp::pair_base(const unsigned int &r) {
  return (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
}

__attribute__((pure)) unsigned int
GetPairBoundProp::get_pair(const GetPairBoundProp::state &s,
                           const unsigned int &r) {
  unsigned int base = pair_base(r);
  return (((16u ? get_reg(s, base) % 16u : get_reg(s, base)) * 16u) +
          (16u ? get_reg(s, (base + 1)) % 16u : get_reg(s, (base + 1))));
}

__attribute__((pure)) List<unsigned int>
GetPairBoundProp::set_pair(const GetPairBoundProp::state &s,
                           const unsigned int &r, const unsigned int &v) {
  unsigned int base = pair_base(r);
  unsigned int hi = (16u ? (16u ? v / 16u : 0) % 16u : (16u ? v / 16u : 0));
  unsigned int lo = (16u ? v % 16u : v);
  return update_nth<unsigned int>(
      (base + 1), lo, update_nth<unsigned int>(base, hi, s.ex_regs));
}

__attribute__((pure)) List<unsigned int>
GetPairBoundProp::push_return(const GetPairBoundProp::state &s,
                              const unsigned int &ret) {
  return List<unsigned int>::cons((4096u ? ret % 4096u : ret), s.ex_stack)
      .firstn(2u);
}

__attribute__((pure)) GetPairBoundProp::state
GetPairBoundProp::execute(const GetPairBoundProp::state &s,
                          const GetPairBoundProp::instr &i) {
  if (std::holds_alternative<typename GetPairBoundProp::instr::NOP>(i.v())) {
    return state{s.ex_acc,   s.ex_regs,
                 s.ex_carry, (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::LDM>(
                 i.v())) {
    const auto &[d_n] = std::get<typename GetPairBoundProp::instr::LDM>(i.v());
    return state{(16u ? d_n % 16u : d_n),
                 s.ex_regs,
                 s.ex_carry,
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::LD>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::LD>(i.v());
    return state{
        get_reg(s, d_r), s.ex_regs,
        s.ex_carry,      (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
        s.ex_stack,      s.ex_pair_bus,
        s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::XCH>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::XCH>(i.v());
    unsigned int regv = get_reg(s, d_r);
    return state{regv,       set_reg(s, d_r, s.ex_acc),
                 s.ex_carry, (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::INC>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::INC>(i.v());
    return state{s.ex_acc,   set_reg(s, d_r, (get_reg(s, d_r) + 1)),
                 s.ex_carry, (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::ADD>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::ADD>(i.v());
    unsigned int sum = ((s.ex_acc + get_reg(s, d_r)) + [&]() -> unsigned int {
      if (s.ex_carry) {
        return 1u;
      } else {
        return 0u;
      }
    }());
    return state{(16u ? sum % 16u : sum),
                 s.ex_regs,
                 16u <= sum,
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::SUB>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::SUB>(i.v());
    unsigned int diff =
        ((((s.ex_acc + 16u) - get_reg(s, d_r)) > (s.ex_acc + 16u)
              ? 0
              : ((s.ex_acc + 16u) - get_reg(s, d_r))));
    return state{(16u ? diff % 16u : diff),
                 s.ex_regs,
                 get_reg(s, d_r) <= s.ex_acc,
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::IAC>(
                 i.v())) {
    return state{(16u ? (s.ex_acc + 1) % 16u : (s.ex_acc + 1)),
                 s.ex_regs,
                 16u <= (s.ex_acc + 1),
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::DAC>(
                 i.v())) {
    return state{(16u ? (s.ex_acc + 15u) % 16u : (s.ex_acc + 15u)),
                 s.ex_regs,
                 !(s.ex_acc == 0u),
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CLC>(
                 i.v())) {
    return state{s.ex_acc,   s.ex_regs,
                 false,      (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::STC>(
                 i.v())) {
    return state{s.ex_acc,   s.ex_regs,
                 true,       (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CMC>(
                 i.v())) {
    return state{
        s.ex_acc,      s.ex_regs,
        !(s.ex_carry), (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
        s.ex_stack,    s.ex_pair_bus,
        s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CMA>(
                 i.v())) {
    return state{(((15u - s.ex_acc) > 15u ? 0 : (15u - s.ex_acc))),
                 s.ex_regs,
                 s.ex_carry,
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::CLB>(
                 i.v())) {
    return state{0u,         s.ex_regs,
                 false,      (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::RAL>(
                 i.v())) {
    unsigned int acc_ = (16u ? ((2u * s.ex_acc) + [&]() -> unsigned int {
                                 if (s.ex_carry) {
                                   return 1u;
                                 } else {
                                   return 0u;
                                 }
                               }()) %
                                   16u
                             : ((2u * s.ex_acc) + [&]() -> unsigned int {
                                 if (s.ex_carry) {
                                   return 1u;
                                 } else {
                                   return 0u;
                                 }
                               }()));
    bool carry_ = 16u <= ((2u * s.ex_acc) + [&]() -> unsigned int {
                    if (s.ex_carry) {
                      return 1u;
                    } else {
                      return 0u;
                    }
                  }());
    return state{acc_,       s.ex_regs,
                 carry_,     (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::RAR>(
                 i.v())) {
    unsigned int carry_bit;
    if (s.ex_carry) {
      carry_bit = 8u;
    } else {
      carry_bit = 0u;
    }
    return state{((2u ? s.ex_acc / 2u : 0) + carry_bit),
                 s.ex_regs,
                 (2u ? s.ex_acc % 2u : s.ex_acc) == 1u,
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::TCC>(
                 i.v())) {
    return state{[&]() -> unsigned int {
                   if (s.ex_carry) {
                     return 1u;
                   } else {
                     return 0u;
                   }
                 }(),
                 s.ex_regs,
                 false,
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::TCS>(
                 i.v())) {
    return state{[&]() -> unsigned int {
                   if (s.ex_carry) {
                     return 10u;
                   } else {
                     return 9u;
                   }
                 }(),
                 s.ex_regs,
                 false,
                 (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::DAA>(
                 i.v())) {
    unsigned int acc_;
    if (10u <= (s.ex_acc + 1)) {
      acc_ = (16u ? (s.ex_acc + 6u) % 16u : (s.ex_acc + 6u));
    } else {
      acc_ = s.ex_acc;
    }
    return state{acc_,       s.ex_regs,
                 s.ex_carry, (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::KBP>(
                 i.v())) {
    unsigned int a = s.ex_acc;
    unsigned int out;
    if (a == 0u) {
      out = 0u;
    } else {
      if (a == 1u) {
        out = 0u;
      } else {
        if (a == 2u) {
          out = 1u;
        } else {
          if (a == 4u) {
            out = 2u;
          } else {
            if (a == 8u) {
              out = 3u;
            } else {
              out = 15u;
            }
          }
        }
      }
    }
    return state{out,        s.ex_regs,
                 s.ex_carry, (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JUN>(
                 i.v())) {
    const auto &[d_a] = std::get<typename GetPairBoundProp::instr::JUN>(i.v());
    return state{
        s.ex_acc,   s.ex_regs,     s.ex_carry, (4096u ? d_a % 4096u : d_a),
        s.ex_stack, s.ex_pair_bus, s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JMS>(
                 i.v())) {
    const auto &[d_a] = std::get<typename GetPairBoundProp::instr::JMS>(i.v());
    return state{s.ex_acc,
                 s.ex_regs,
                 s.ex_carry,
                 (4096u ? d_a % 4096u : d_a),
                 push_return(s, (s.ex_pc + 2u)),
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JCN>(
                 i.v())) {
    const auto &[d_c, d_a] =
        std::get<typename GetPairBoundProp::instr::JCN>(i.v());
    bool jump = ((2u ? d_c % 2u : d_c) == 1u && s.ex_carry);
    return state{s.ex_acc,
                 s.ex_regs,
                 s.ex_carry,
                 [&]() -> unsigned int {
                   if (jump) {
                     return (4096u ? d_a % 4096u : d_a);
                   } else {
                     return (4096u ? (s.ex_pc + 2u) % 4096u : (s.ex_pc + 2u));
                   }
                 }(),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::FIM>(
                 i.v())) {
    const auto &[d_r, d_d] =
        std::get<typename GetPairBoundProp::instr::FIM>(i.v());
    return state{s.ex_acc,   set_pair(s, d_r, d_d),
                 s.ex_carry, (4096u ? (s.ex_pc + 2u) % 4096u : (s.ex_pc + 2u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::SRC>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::SRC>(i.v());
    return state{s.ex_acc,   s.ex_regs,
                 s.ex_carry, (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, get_pair(s, d_r),
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::FIN>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::FIN>(i.v());
    return state{s.ex_acc,   set_pair(s, d_r, s.ex_pair_bus),
                 s.ex_carry, (4096u ? (s.ex_pc + 1u) % 4096u : (s.ex_pc + 1u)),
                 s.ex_stack, s.ex_pair_bus,
                 s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::JIN>(
                 i.v())) {
    const auto &[d_r] = std::get<typename GetPairBoundProp::instr::JIN>(i.v());
    return state{
        s.ex_acc,   s.ex_regs,
        s.ex_carry, (4096u ? get_pair(s, d_r) % 4096u : get_pair(s, d_r)),
        s.ex_stack, s.ex_pair_bus,
        s.ex_ports};
  } else if (std::holds_alternative<typename GetPairBoundProp::instr::ISZ>(
                 i.v())) {
    const auto &[d_r, d_a] =
        std::get<typename GetPairBoundProp::instr::ISZ>(i.v());
    unsigned int n =
        (16u ? (get_reg(s, d_r) + 1) % 16u : (get_reg(s, d_r) + 1));
    return state{s.ex_acc,
                 set_reg(s, d_r, n),
                 s.ex_carry,
                 [&]() -> unsigned int {
                   if (n == 0u) {
                     return (4096u ? d_a % 4096u : d_a);
                   } else {
                     return (4096u ? (s.ex_pc + 2u) % 4096u : (s.ex_pc + 2u));
                   }
                 }(),
                 s.ex_stack,
                 s.ex_pair_bus,
                 s.ex_ports};
  } else {
    const auto &[d_d] = std::get<typename GetPairBoundProp::instr::BBL>(i.v());
    return state{(16u ? d_d % 16u : d_d),
                 s.ex_regs,
                 s.ex_carry,
                 ListDef::template nth<unsigned int>(0u, s.ex_stack, 0u),
                 s.ex_stack.skipn(1u),
                 s.ex_pair_bus,
                 s.ex_ports};
  }
}
