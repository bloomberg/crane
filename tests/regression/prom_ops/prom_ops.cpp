#include <prom_ops.h>

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

__attribute__((pure)) bool
PromOps::nat_list_eqb(const std::shared_ptr<List<unsigned int>> &xs,
                      const std::shared_ptr<List<unsigned int>> &ys) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil _args) -> bool {
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil _args) -> bool {
                      return true;
                    },
                    [](const typename List<unsigned int>::Cons _args) -> bool {
                      return false;
                    }},
                ys->v());
          },
          [&](const typename List<unsigned int>::Cons _args) -> bool {
            unsigned int x = _args.d_a0;
            std::shared_ptr<List<unsigned int>> xs_ = _args.d_a1;
            return std::visit(
                Overloaded{
                    [](const typename List<unsigned int>::Nil _args) -> bool {
                      return false;
                    },
                    [&](const typename List<unsigned int>::Cons _args) -> bool {
                      unsigned int y = _args.d_a0;
                      std::shared_ptr<List<unsigned int>> ys_ = _args.d_a1;
                      return (std::move(x) == std::move(y) &&
                              nat_list_eqb(std::move(xs_), std::move(ys_)));
                    }},
                ys->v());
          }},
      xs->v());
}

__attribute__((pure)) unsigned int
PromOps::prom_data_or_zero(const std::shared_ptr<PromOps::state1> &s) {
  if (s->prom_enable1) {
    return s->prom_data1;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
PromOps::flagged_sum(const std::shared_ptr<PromOps::state2> &s) {
  return ((s->acc2 + s->prom_addr2) + [&](void) {
    if (s->prom_enable2) {
      return s->prom_data2;
    } else {
      return 0u;
    }
  }());
}

std::shared_ptr<PromOps::state3>
PromOps::set_prom_params3(std::shared_ptr<PromOps::state3> s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state3>(state3{
      s->acc3, s->regs3, s->carry3, s->pc3, s->stack3, s->ram_sys3,
      s->cur_bank3, s->sel_ram3, s->rom_ports3, s->sel_rom3, s->rom3,
      s->test_pin3, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<PromOps::state5>
PromOps::set_prom_params5(std::shared_ptr<PromOps::state5> s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state5>(
      state5{s->acc5, s->regs5, s->rom5, std::move(addr), std::move(data),
             std::move(enable)});
}

std::shared_ptr<PromOps::state6>
PromOps::set_prom_params6(std::shared_ptr<PromOps::state6> s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state6>(state6{
      std::move(s)->rom6, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<PromOps::state7>
PromOps::set_prom_params7(std::shared_ptr<PromOps::state7> s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state7>(
      state7{s->regs7, s->ram_sys7, std::move(addr), std::move(data),
             std::move(enable)});
}

std::shared_ptr<PromOps::state8>
PromOps::set_prom_params8(std::shared_ptr<PromOps::state8> s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state8>(
      state8{s->regs8, s->ram_sys8, std::move(addr), std::move(data),
             std::move(enable)});
}

std::shared_ptr<PromOps::state9>
PromOps::set_prom_params9(std::shared_ptr<PromOps::state9> s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state9>(state9{
      std::move(s)->rom9, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<PromOps::state10>
PromOps::set_prom_params10(std::shared_ptr<PromOps::state10> s,
                           const unsigned int addr, const unsigned int data,
                           const bool enable) {
  return std::make_shared<PromOps::state10>(
      state10{s->regs10, s->rom10, s->acc10, s->pc10, s->stack10, s->cur_bank10,
              s->rom_ports10, s->sel_rom10, std::move(addr), std::move(data),
              std::move(enable)});
}

std::shared_ptr<PromOps::state10>
PromOps::execute_wpm10(std::shared_ptr<PromOps::state10> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable10) {
    new_rom =
        update_nth<unsigned int>(s->prom_addr10, s->prom_data10, s->rom10);
  } else {
    new_rom = std::move(s)->rom10;
  }
  return std::make_shared<PromOps::state10>(
      state10{s->regs10, std::move(new_rom), s->acc10, s->pc10, s->stack10,
              s->cur_bank10, s->rom_ports10, s->sel_rom10, s->prom_addr10,
              s->prom_data10, s->prom_enable10});
}

std::shared_ptr<PromOps::state11>
PromOps::execute_wpm11(std::shared_ptr<PromOps::state11> s) {
  if (s->prom_enable11) {
    return std::make_shared<PromOps::state11>(state11{
        update_nth<unsigned int>(s->prom_addr11, s->prom_data11, s->rom11),
        s->prom_addr11, s->prom_data11, s->prom_enable11});
  } else {
    return std::move(s);
  }
}

__attribute__((pure)) bool Bool::eqb(const bool b1, const bool b2) {
  if (b1) {
    if (b2) {
      return true;
    } else {
      return false;
    }
  } else {
    if (b2) {
      return false;
    } else {
      return true;
    }
  }
}
