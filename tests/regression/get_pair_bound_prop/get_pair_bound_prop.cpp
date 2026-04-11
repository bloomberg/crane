#include <get_pair_bound_prop.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
GetPairBoundProp::get_reg(const std::shared_ptr<GetPairBoundProp::state> &s,
                          const unsigned int r) {
  return s->ex_regs->nth(r, 0u);
}

std::shared_ptr<List<unsigned int>>
GetPairBoundProp::set_reg(const std::shared_ptr<GetPairBoundProp::state> &s,
                          const unsigned int r, const unsigned int v) {
  return update_nth<unsigned int>(r, (16u ? v % 16u : v), s->ex_regs);
}

__attribute__((pure)) unsigned int
GetPairBoundProp::pair_base(const unsigned int r) {
  return (((r - (2u ? r % 2u : r)) > r ? 0 : (r - (2u ? r % 2u : r))));
}

__attribute__((pure)) unsigned int
GetPairBoundProp::get_pair(const std::shared_ptr<GetPairBoundProp::state> &s,
                           const unsigned int r) {
  unsigned int base = pair_base(r);
  return (((16u ? get_reg(s, base) % 16u : get_reg(s, base)) * 16u) +
          (16u ? get_reg(s, (base + 1)) % 16u : get_reg(s, (base + 1))));
}

std::shared_ptr<List<unsigned int>>
GetPairBoundProp::set_pair(const std::shared_ptr<GetPairBoundProp::state> &s,
                           const unsigned int r, const unsigned int v) {
  unsigned int base = pair_base(r);
  unsigned int hi = (16u ? (16u ? v / 16u : 0) % 16u : (16u ? v / 16u : 0));
  unsigned int lo = (16u ? v % 16u : v);
  return update_nth<unsigned int>(
      (base + 1), lo, update_nth<unsigned int>(base, hi, s->ex_regs));
}

std::shared_ptr<List<unsigned int>>
GetPairBoundProp::push_return(std::shared_ptr<GetPairBoundProp::state> s,
                              const unsigned int ret) {
  return List<unsigned int>::cons((4096u ? ret % 4096u : ret), s->ex_stack)
      ->firstn(2u);
}

std::shared_ptr<GetPairBoundProp::state>
GetPairBoundProp::execute(std::shared_ptr<GetPairBoundProp::state> s,
                          const std::shared_ptr<GetPairBoundProp::instr> &i) {
  return std::visit(
      Overloaded{
          [&](const typename GetPairBoundProp::instr::NOP _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, s->ex_carry,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::LDM _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(state{
                (16u ? _args.d_n % 16u : _args.d_n), s->ex_regs, s->ex_carry,
                (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::LD _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{get_reg(s, _args.d_r), s->ex_regs, s->ex_carry,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::XCH _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            unsigned int regv = get_reg(s, _args.d_r);
            return std::make_shared<GetPairBoundProp::state>(
                state{regv, set_reg(s, _args.d_r, s->ex_acc), s->ex_carry,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::INC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(state{
                s->ex_acc, set_reg(s, _args.d_r, (get_reg(s, _args.d_r) + 1)),
                s->ex_carry,
                (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::ADD _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            unsigned int sum =
                ((s->ex_acc + get_reg(s, _args.d_r)) + [&]() -> unsigned int {
                  if (s->ex_carry) {
                    return 1u;
                  } else {
                    return 0u;
                  }
                }());
            return std::make_shared<GetPairBoundProp::state>(
                state{(16u ? sum % 16u : sum), s->ex_regs, 16u <= sum,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::SUB _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            unsigned int diff = ((
                ((s->ex_acc + 16u) - get_reg(s, _args.d_r)) > (s->ex_acc + 16u)
                    ? 0
                    : ((s->ex_acc + 16u) - get_reg(s, _args.d_r))));
            return std::make_shared<GetPairBoundProp::state>(
                state{(16u ? diff % 16u : diff), s->ex_regs,
                      get_reg(s, _args.d_r) <= s->ex_acc,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::IAC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{(16u ? (s->ex_acc + 1) % 16u : (s->ex_acc + 1)),
                      s->ex_regs, 16u <= (s->ex_acc + 1),
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::DAC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{(16u ? (s->ex_acc + 15u) % 16u : (s->ex_acc + 15u)),
                      s->ex_regs, !(s->ex_acc == 0u),
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::CLC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, false,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::STC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, true,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::CMC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, !(s->ex_carry),
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::CMA _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{(((15u - s->ex_acc) > 15u ? 0 : (15u - s->ex_acc))),
                      s->ex_regs, s->ex_carry,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::CLB _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{0u, s->ex_regs, false,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::RAL _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            unsigned int acc_ =
                (16u ? ((2u * s->ex_acc) + [&]() -> unsigned int {
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
            return std::make_shared<GetPairBoundProp::state>(
                state{acc_, s->ex_regs, carry_,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::RAR _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            unsigned int carry_bit;
            if (s->ex_carry) {
              carry_bit = 8u;
            } else {
              carry_bit = 0u;
            }
            return std::make_shared<GetPairBoundProp::state>(
                state{((2u ? s->ex_acc / 2u : 0) + carry_bit), s->ex_regs,
                      (2u ? s->ex_acc % 2u : s->ex_acc) == 1u,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::TCC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{[&]() -> unsigned int {
                        if (s->ex_carry) {
                          return 1u;
                        } else {
                          return 0u;
                        }
                      }(),
                      s->ex_regs, false,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::TCS _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{[&]() -> unsigned int {
                        if (s->ex_carry) {
                          return 10u;
                        } else {
                          return 9u;
                        }
                      }(),
                      s->ex_regs, false,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::DAA _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            unsigned int acc_;
            if (10u <= (s->ex_acc + 1)) {
              acc_ = (16u ? (s->ex_acc + 6u) % 16u : (s->ex_acc + 6u));
            } else {
              acc_ = s->ex_acc;
            }
            return std::make_shared<GetPairBoundProp::state>(
                state{acc_, s->ex_regs, s->ex_carry,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::KBP _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
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
            return std::make_shared<GetPairBoundProp::state>(
                state{out, s->ex_regs, s->ex_carry,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::JUN _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, s->ex_carry,
                      (4096u ? _args.d_a % 4096u : _args.d_a), s->ex_stack,
                      s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::JMS _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(state{
                s->ex_acc, s->ex_regs, s->ex_carry,
                (4096u ? _args.d_a % 4096u : _args.d_a),
                push_return(s, (s->ex_pc + 2u)), s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::JCN _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            bool jump =
                ((2u ? _args.d_c % 2u : _args.d_c) == 1u && s->ex_carry);
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, s->ex_carry,
                      [&]() -> unsigned int {
                        if (jump) {
                          return (4096u ? _args.d_a % 4096u : _args.d_a);
                        } else {
                          return (4096u ? (std::move(s)->ex_pc + 2u) % 4096u
                                        : (std::move(s)->ex_pc + 2u));
                        }
                      }(),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::FIM _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, set_pair(s, _args.d_r, _args.d_d), s->ex_carry,
                      (4096u ? (s->ex_pc + 2u) % 4096u : (s->ex_pc + 2u)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::SRC _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, s->ex_carry,
                      (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                      s->ex_stack, get_pair(s, _args.d_r), s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::FIN _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(state{
                s->ex_acc, set_pair(s, _args.d_r, s->ex_pair_bus), s->ex_carry,
                (4096u ? (s->ex_pc + 1u) % 4096u : (s->ex_pc + 1u)),
                s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::JIN _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, s->ex_regs, s->ex_carry,
                      (4096u ? get_pair(s, _args.d_r) % 4096u
                             : get_pair(s, _args.d_r)),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::ISZ _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            unsigned int n = (16u ? (get_reg(s, _args.d_r) + 1) % 16u
                                  : (get_reg(s, _args.d_r) + 1));
            return std::make_shared<GetPairBoundProp::state>(
                state{s->ex_acc, set_reg(s, _args.d_r, n), s->ex_carry,
                      [&]() -> unsigned int {
                        if (n == 0u) {
                          return (4096u ? _args.d_a % 4096u : _args.d_a);
                        } else {
                          return (4096u ? (std::move(s)->ex_pc + 2u) % 4096u
                                        : (std::move(s)->ex_pc + 2u));
                        }
                      }(),
                      s->ex_stack, s->ex_pair_bus, s->ex_ports});
          },
          [&](const typename GetPairBoundProp::instr::BBL _args)
              -> std::shared_ptr<GetPairBoundProp::state> {
            return std::make_shared<GetPairBoundProp::state>(
                state{(16u ? _args.d_d % 16u : _args.d_d), s->ex_regs,
                      s->ex_carry, s->ex_stack->nth(0u, 0u),
                      s->ex_stack->skipn(1u), s->ex_pair_bus, s->ex_ports});
          }},
      i->v());
}
