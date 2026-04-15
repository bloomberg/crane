#include <cpu_emulator.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
CpuEmulator::get_reg(const std::shared_ptr<CpuEmulator::state> &s,
                     const unsigned int r) {
  return s->ex_regs->nth(r, 0u);
}

std::shared_ptr<List<unsigned int>>
CpuEmulator::set_reg(const std::shared_ptr<CpuEmulator::state> &s,
                     const unsigned int r, const unsigned int v) {
  return update_nth<unsigned int>(r, (16u ? v % 16u : v), s->ex_regs);
}

__attribute__((pure)) unsigned int
CpuEmulator::pair_base(const unsigned int r) {
  return (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
}

__attribute__((pure)) unsigned int
CpuEmulator::get_pair(const std::shared_ptr<CpuEmulator::state> &s,
                      const unsigned int r) {
  unsigned int base = pair_base(r);
  return (((16u ? get_reg(s, base) % 16u : get_reg(s, base)) * 16u) +
          (16u ? get_reg(s, (base + 1)) % 16u : get_reg(s, (base + 1))));
}

std::shared_ptr<List<unsigned int>>
CpuEmulator::set_pair(const std::shared_ptr<CpuEmulator::state> &s,
                      const unsigned int r, const unsigned int v) {
  unsigned int base = pair_base(r);
  unsigned int hi = (16u ? (16u ? v / 16u : 0) % 16u : (16u ? v / 16u : 0));
  unsigned int lo = (16u ? v % 16u : v);
  return update_nth<unsigned int>(
      (base + 1), lo, update_nth<unsigned int>(base, hi, s->ex_regs));
}

std::shared_ptr<List<unsigned int>>
CpuEmulator::push_return(const std::shared_ptr<CpuEmulator::state> &s,
                         const unsigned int ret) {
  return List<unsigned int>::cons((4096u ? ret % 4096u : ret), s->ex_stack)
      ->firstn(2u);
}

std::shared_ptr<CpuEmulator::state>
CpuEmulator::execute(const std::shared_ptr<CpuEmulator::state> &s,
                     const std::shared_ptr<CpuEmulator::instr> &i) {
  if (std::holds_alternative<typename CpuEmulator::instr::NOP>(i->v())) {
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, s->ex_regs, s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::LDM>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::LDM>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{(16u ? _m.d_n % 16u : _m.d_n), s->ex_regs, s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::LD>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::LD>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{get_reg(s, _m.d_r), s->ex_regs, s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::XCH>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::XCH>(&i->v());
    unsigned int regv = get_reg(s, _m.d_r);
    return std::make_shared<CpuEmulator::state>(
        state{regv, set_reg(s, _m.d_r, s->ex_acc), s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::INC>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::INC>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, set_reg(s, _m.d_r, (get_reg(s, _m.d_r) + 1)),
              s->ex_carry, (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
              s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::ADD>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::ADD>(&i->v());
    unsigned int sum =
        ((s->ex_acc + get_reg(s, _m.d_r)) + [&]() -> unsigned int {
          if (s->ex_carry) {
            return 1u;
          } else {
            return 0u;
          }
        }());
    return std::make_shared<CpuEmulator::state>(
        state{(16u ? sum % 16u : sum), s->ex_regs, 16u <= sum,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::SUB>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::SUB>(&i->v());
    unsigned int diff =
        ((((s->ex_acc + 16u) - get_reg(s, _m.d_r)) > (s->ex_acc + 16u)
              ? 0
              : ((s->ex_acc + 16u) - get_reg(s, _m.d_r))));
    return std::make_shared<CpuEmulator::state>(state{
        (16u ? diff % 16u : diff), s->ex_regs, get_reg(s, _m.d_r) <= s->ex_acc,
        (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
        s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::IAC>(i->v())) {
    return std::make_shared<CpuEmulator::state>(
        state{(16u ? (s->ex_acc + 1) % 16u : (s->ex_acc + 1)), s->ex_regs,
              16u <= (s->ex_acc + 1),
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::DAC>(i->v())) {
    return std::make_shared<CpuEmulator::state>(state{
        (16u ? (s->ex_acc + 15u) % 16u : (s->ex_acc + 15u)), s->ex_regs,
        !(s->ex_acc == 0u), (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
        s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::CLC>(i->v())) {
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, s->ex_regs, false,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::STC>(i->v())) {
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, s->ex_regs, true,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::CMC>(i->v())) {
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, s->ex_regs, !(s->ex_carry),
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::CMA>(i->v())) {
    return std::make_shared<CpuEmulator::state>(
        state{(((15u - s->ex_acc) > 15u ? 0 : (15u - s->ex_acc))), s->ex_regs,
              s->ex_carry, (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
              s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::CLB>(i->v())) {
    return std::make_shared<CpuEmulator::state>(
        state{0u, s->ex_regs, false,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::RAL>(i->v())) {
    unsigned int acc_ = (16u ? ((2u * s->ex_acc) + [&]() -> unsigned int {
                                 if (s->ex_carry) {
                                   return 1u;
                                 } else {
                                   return 0u;
                                 }
                               }()) %
                                   16u
                             : ((2u * s->ex_acc) + [&]() -> unsigned int {
                                 if (s->ex_carry) {
                                   return 1u;
                                 } else {
                                   return 0u;
                                 }
                               }()));
    bool carry_ = 16u <= ((2u * s->ex_acc) + [&]() -> unsigned int {
                    if (s->ex_carry) {
                      return 1u;
                    } else {
                      return 0u;
                    }
                  }());
    return std::make_shared<CpuEmulator::state>(
        state{acc_, s->ex_regs, carry_,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::RAR>(i->v())) {
    unsigned int carry_bit;
    if (s->ex_carry) {
      carry_bit = 8u;
    } else {
      carry_bit = 0u;
    }
    return std::make_shared<CpuEmulator::state>(
        state{((2u ? s->ex_acc / 2u : 0) + carry_bit), s->ex_regs,
              (2u ? s->ex_acc % 2u : s->ex_acc) == 1u,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::TCC>(i->v())) {
    return std::make_shared<CpuEmulator::state>(state{
        [&]() -> unsigned int {
          if (s->ex_carry) {
            return 1u;
          } else {
            return 0u;
          }
        }(),
        s->ex_regs, false, (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
        s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::TCS>(i->v())) {
    return std::make_shared<CpuEmulator::state>(state{
        [&]() -> unsigned int {
          if (s->ex_carry) {
            return 10u;
          } else {
            return 9u;
          }
        }(),
        s->ex_regs, false, (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
        s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::DAA>(i->v())) {
    unsigned int acc_;
    if (10u <= (s->ex_acc + 1)) {
      acc_ = (16u ? (s->ex_acc + 6u) % 16u : (s->ex_acc + 6u));
    } else {
      acc_ = s->ex_acc;
    }
    return std::make_shared<CpuEmulator::state>(
        state{acc_, s->ex_regs, s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::KBP>(i->v())) {
    unsigned int a = s->ex_acc;
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
    return std::make_shared<CpuEmulator::state>(
        state{out, s->ex_regs, s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::JUN>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::JUN>(&i->v());
    return std::make_shared<CpuEmulator::state>(state{
        s->ex_acc, s->ex_regs, s->ex_carry, (4096u ? _m.d_a % 4096u : _m.d_a),
        s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::JMS>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::JMS>(&i->v());
    return std::make_shared<CpuEmulator::state>(state{
        s->ex_acc, s->ex_regs, s->ex_carry, (4096u ? _m.d_a % 4096u : _m.d_a),
        push_return(s, (s->ex_pc + 2u)), s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::JCN>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::JCN>(&i->v());
    bool jump = ((2u ? _m.d_c % 2u : _m.d_c) == 1u && s->ex_carry);
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, s->ex_regs, s->ex_carry,
              [&]() -> unsigned int {
                if (jump) {
                  return (4096u ? _m.d_a % 4096u : _m.d_a);
                } else {
                  return (4096u ? (s->ex_pc + 2u) % 4096u : (s->ex_pc + 2u));
                }
              }(),
              s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::FIM>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::FIM>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, set_pair(s, _m.d_r, _m.d_d), s->ex_carry,
              (4096u ? (s->ex_pc + 2u) % 4096u : (s->ex_pc + 2u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::SRC>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::SRC>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, s->ex_regs, s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              get_pair(s, _m.d_r), s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::FIN>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::FIN>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, set_pair(s, _m.d_r, s->ex_pair_bus), s->ex_carry,
              (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)), s->ex_stack,
              s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::JIN>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::JIN>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, s->ex_regs, s->ex_carry,
              (4096u ? get_pair(s, _m.d_r) % 4096u : get_pair(s, _m.d_r)),
              s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else if (std::holds_alternative<typename CpuEmulator::instr::ISZ>(i->v())) {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::ISZ>(&i->v());
    unsigned int n =
        (16u ? (get_reg(s, _m.d_r) + 1) % 16u : (get_reg(s, _m.d_r) + 1));
    return std::make_shared<CpuEmulator::state>(
        state{s->ex_acc, set_reg(s, _m.d_r, n), s->ex_carry,
              [&]() -> unsigned int {
                if (n == 0u) {
                  return (4096u ? _m.d_a % 4096u : _m.d_a);
                } else {
                  return (4096u ? (s->ex_pc + 2u) % 4096u : (s->ex_pc + 2u));
                }
              }(),
              s->ex_stack, s->ex_pair_bus, s->ex_ports});
  } else {
    const auto &_m = *std::get_if<typename CpuEmulator::instr::BBL>(&i->v());
    return std::make_shared<CpuEmulator::state>(
        state{(16u ? _m.d_d % 16u : _m.d_d), s->ex_regs, s->ex_carry,
              s->ex_stack->nth(0u, 0u), s->ex_stack->skipn(1u), s->ex_pair_bus,
              s->ex_ports});
  }
}
