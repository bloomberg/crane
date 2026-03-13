#include <cpu_emulator.h>

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

__attribute__((pure)) unsigned int
CpuEmulator::get_reg(const std::shared_ptr<CpuEmulator::state> &s,
                     const unsigned int r) {
  return s->ex_regs->nth(r, 0u);
}

std::shared_ptr<List<unsigned int>>
CpuEmulator::set_reg(const std::shared_ptr<CpuEmulator::state> &s,
                     const unsigned int r, const unsigned int v) {
  return update_nth<unsigned int>(r, (v % 16u), s->ex_regs);
}

__attribute__((pure)) unsigned int
CpuEmulator::pair_base(const unsigned int r) {
  return (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))));
}

__attribute__((pure)) unsigned int
CpuEmulator::get_pair(const std::shared_ptr<CpuEmulator::state> &s,
                      const unsigned int r) {
  unsigned int base = pair_base(r);
  return (((get_reg(s, base) % 16u) * 16u) + (get_reg(s, (base + 1)) % 16u));
}

std::shared_ptr<List<unsigned int>>
CpuEmulator::set_pair(const std::shared_ptr<CpuEmulator::state> &s,
                      const unsigned int r, const unsigned int v) {
  unsigned int base = pair_base(r);
  unsigned int hi = (Nat::div(v, 16u) % 16u);
  unsigned int lo = (v % 16u);
  return update_nth<unsigned int>(
      (base + 1), std::move(lo),
      update_nth<unsigned int>(base, std::move(hi), s->ex_regs));
}

std::shared_ptr<List<unsigned int>>
CpuEmulator::push_return(std::shared_ptr<CpuEmulator::state> s,
                         const unsigned int ret) {
  return List<unsigned int>::ctor::Cons_((std::move(ret) % 4096u),
                                         std::move(s)->ex_stack)
      ->firstn(2u);
}

std::shared_ptr<CpuEmulator::state>
CpuEmulator::execute(std::shared_ptr<CpuEmulator::state> s,
                     const std::shared_ptr<CpuEmulator::instr> &i) {
  return std::visit(
      Overloaded{
          [&](const typename CpuEmulator::instr::NOP _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(state{
                s->ex_acc, s->ex_regs, s->ex_carry, ((s->ex_pc + 1u) % 4096u),
                s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::LDM _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int n = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(
                state{(std::move(n) % 16u), s->ex_regs, s->ex_carry,
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::LD _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(
                state{get_reg(s, std::move(r)), s->ex_regs, s->ex_carry,
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::XCH _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            unsigned int regv = get_reg(std::move(s), std::move(r));
            return std::make_shared<CpuEmulator::state>(
                state{std::move(regv), set_reg(s, std::move(r), s->ex_acc),
                      s->ex_carry, ((s->ex_pc + 1u) % 4096u), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::INC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, set_reg(s, r, (get_reg(s, r) + 1)),
                      s->ex_carry, ((s->ex_pc + 1u) % 4096u), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::ADD _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            unsigned int sum =
                ((s->ex_acc + get_reg(s, std::move(r))) + [&](void) {
                  if (s->ex_carry) {
                    return 1u;
                  } else {
                    return 0u;
                  }
                }());
            return std::make_shared<CpuEmulator::state>(state{
                (sum % 16u), s->ex_regs, 16u <= sum, ((s->ex_pc + 1u) % 4096u),
                s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::SUB _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            unsigned int diff =
                ((((s->ex_acc + 16u) - get_reg(s, std::move(r))) >
                          (s->ex_acc + 16u)
                      ? 0
                      : ((s->ex_acc + 16u) - get_reg(s, std::move(r)))));
            return std::make_shared<CpuEmulator::state>(
                state{(std::move(diff) % 16u), s->ex_regs,
                      get_reg(s, std::move(r)) <= s->ex_acc,
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::IAC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{((s->ex_acc + 1) % 16u), s->ex_regs,
                      16u <= (s->ex_acc + 1), ((s->ex_pc + 1u) % 4096u),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::DAC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{((s->ex_acc + 15u) % 16u), s->ex_regs, !(s->ex_acc == 0u),
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::CLC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, s->ex_regs, false, ((s->ex_pc + 1u) % 4096u),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::STC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, s->ex_regs, true, ((s->ex_pc + 1u) % 4096u),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::CMC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, s->ex_regs, !(s->ex_carry),
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::CMA _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{(((15u - s->ex_acc) > 15u ? 0 : (15u - s->ex_acc))),
                      s->ex_regs, s->ex_carry, ((s->ex_pc + 1u) % 4096u),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::CLB _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{0u, s->ex_regs, false, ((s->ex_pc + 1u) % 4096u),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::RAL _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int acc_ = (((2u * s->ex_acc) +
                                  [&](void) {
                                    if (s->ex_carry) {
                                      return 1u;
                                    } else {
                                      return 0u;
                                    }
                                  }()) %
                                 16u);
            bool carry_ = 16u <= ((2u * s->ex_acc) + [&](void) {
                            if (s->ex_carry) {
                              return 1u;
                            } else {
                              return 0u;
                            }
                          }());
            return std::make_shared<CpuEmulator::state>(
                state{std::move(acc_), s->ex_regs, std::move(carry_),
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::RAR _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int carry_bit;
            if (std::move(s)->ex_carry) {
              carry_bit = 8u;
            } else {
              carry_bit = 0u;
            }
            return std::make_shared<CpuEmulator::state>(state{
                (Nat::div(s->ex_acc, 2u) + std::move(carry_bit)), s->ex_regs,
                (s->ex_acc % 2u) == 1u, ((s->ex_pc + 1u) % 4096u), s->ex_stack,
                s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::TCC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{[&](void) {
                        if (s->ex_carry) {
                          return 1u;
                        } else {
                          return 0u;
                        }
                      }(),
                      s->ex_regs, false, ((s->ex_pc + 1u) % 4096u), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::TCS _args)
              -> std::shared_ptr<CpuEmulator::state> {
            return std::make_shared<CpuEmulator::state>(
                state{[&](void) {
                        if (s->ex_carry) {
                          return 10u;
                        } else {
                          return 9u;
                        }
                      }(),
                      s->ex_regs, false, ((s->ex_pc + 1u) % 4096u), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::DAA _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int acc_;
            if (10u <= (s->ex_acc + 1)) {
              acc_ = ((std::move(s)->ex_acc + 6u) % 16u);
            } else {
              acc_ = std::move(s)->ex_acc;
            }
            return std::make_shared<CpuEmulator::state>(
                state{std::move(acc_), s->ex_regs, s->ex_carry,
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::KBP _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int a = std::move(s)->ex_acc;
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
                    if (std::move(a) == 8u) {
                      out = 3u;
                    } else {
                      out = 15u;
                    }
                  }
                }
              }
            }
            return std::make_shared<CpuEmulator::state>(
                state{std::move(out), s->ex_regs, s->ex_carry,
                      ((s->ex_pc + 1u) % 4096u), s->ex_stack, s->ex_pair_bus,
                      s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::JUN _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int a = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(state{
                s->ex_acc, s->ex_regs, s->ex_carry, (std::move(a) % 4096u),
                s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::JMS _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int a = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(state{
                s->ex_acc, s->ex_regs, s->ex_carry, (std::move(a) % 4096u),
                push_return(s, (s->ex_pc + 2u)), s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::JCN _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int c = _args.d_a0;
            unsigned int a = _args.d_a1;
            bool jump = ((std::move(c) % 2u) == 1u && std::move(s)->ex_carry);
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, s->ex_regs, s->ex_carry,
                      [&](void) {
                        if (std::move(jump)) {
                          return (std::move(a) % 4096u);
                        } else {
                          return ((std::move(s)->ex_pc + 2u) % 4096u);
                        }
                      }(),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::FIM _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            unsigned int d = _args.d_a1;
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, set_pair(s, std::move(r), std::move(d)),
                      s->ex_carry, ((s->ex_pc + 2u) % 4096u), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::SRC _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(state{
                s->ex_acc, s->ex_regs, s->ex_carry, ((s->ex_pc + 1u) % 4096u),
                s->ex_stack, get_pair(s, std::move(r)), s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::FIN _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, set_pair(s, std::move(r), s->ex_pair_bus),
                      s->ex_carry, ((s->ex_pc + 1u) % 4096u), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::JIN _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, s->ex_regs, s->ex_carry,
                      (get_pair(s, std::move(r)) % 4096u), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::ISZ _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int r = _args.d_a0;
            unsigned int a = _args.d_a1;
            unsigned int n = ((get_reg(std::move(s), std::move(r)) + 1) % 16u);
            return std::make_shared<CpuEmulator::state>(
                state{s->ex_acc, set_reg(s, std::move(r), n), s->ex_carry,
                      [&](void) {
                        if (n == 0u) {
                          return (std::move(a) % 4096u);
                        } else {
                          return ((std::move(s)->ex_pc + 2u) % 4096u);
                        }
                      }(),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename CpuEmulator::instr::BBL _args)
              -> std::shared_ptr<CpuEmulator::state> {
            unsigned int d = _args.d_a0;
            return std::make_shared<CpuEmulator::state>(
                state{(std::move(d) % 16u), s->ex_regs, s->ex_carry,
                      s->ex_stack->nth(0u, 0u), s->ex_stack->skipn(1u),
                      s->ex_pair_bus, s->ex_ports});
          }},
      i->v());
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
