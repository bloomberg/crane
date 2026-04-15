#include <prom_ops.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool
PromOps::nat_list_eqb(const std::shared_ptr<List<unsigned int>> &xs,
                      const std::shared_ptr<List<unsigned int>> &ys) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(xs->v())) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(ys->v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(xs->v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(ys->v())) {
      return false;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(ys->v());
      return (d_a0 == d_a00 && nat_list_eqb(d_a1, d_a10));
    }
  }
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
  return ((s->acc2 + s->prom_addr2) + [&]() -> unsigned int {
    if (s->prom_enable2) {
      return s->prom_data2;
    } else {
      return 0u;
    }
  }());
}

std::shared_ptr<PromOps::state3>
PromOps::set_prom_params3(const std::shared_ptr<PromOps::state3> &s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state3>(
      state3{s->acc3, s->regs3, s->carry3, s->pc3, s->stack3, s->ram_sys3,
             s->cur_bank3, s->sel_ram3, s->rom_ports3, s->sel_rom3, s->rom3,
             s->test_pin3, addr, data, enable});
}

std::shared_ptr<PromOps::state5>
PromOps::set_prom_params5(const std::shared_ptr<PromOps::state5> &s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state5>(
      state5{s->acc5, s->regs5, s->rom5, addr, data, enable});
}

std::shared_ptr<PromOps::state6>
PromOps::set_prom_params6(const std::shared_ptr<PromOps::state6> &s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state6>(state6{s->rom6, addr, data, enable});
}

std::shared_ptr<PromOps::state7>
PromOps::set_prom_params7(const std::shared_ptr<PromOps::state7> &s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state7>(
      state7{s->regs7, s->ram_sys7, addr, data, enable});
}

std::shared_ptr<PromOps::state8>
PromOps::set_prom_params8(const std::shared_ptr<PromOps::state8> &s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state8>(
      state8{s->regs8, s->ram_sys8, addr, data, enable});
}

std::shared_ptr<PromOps::state9>
PromOps::set_prom_params9(const std::shared_ptr<PromOps::state9> &s,
                          const unsigned int addr, const unsigned int data,
                          const bool enable) {
  return std::make_shared<PromOps::state9>(state9{s->rom9, addr, data, enable});
}

std::shared_ptr<PromOps::state10>
PromOps::set_prom_params10(const std::shared_ptr<PromOps::state10> &s,
                           const unsigned int addr, const unsigned int data,
                           const bool enable) {
  return std::make_shared<PromOps::state10>(
      state10{s->regs10, s->rom10, s->acc10, s->pc10, s->stack10, s->cur_bank10,
              s->rom_ports10, s->sel_rom10, addr, data, enable});
}

std::shared_ptr<PromOps::state10>
PromOps::execute_wpm10(const std::shared_ptr<PromOps::state10> &s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable10) {
    new_rom =
        update_nth<unsigned int>(s->prom_addr10, s->prom_data10, s->rom10);
  } else {
    new_rom = s->rom10;
  }
  return std::make_shared<PromOps::state10>(
      state10{s->regs10, new_rom, s->acc10, s->pc10, s->stack10, s->cur_bank10,
              s->rom_ports10, s->sel_rom10, s->prom_addr10, s->prom_data10,
              s->prom_enable10});
}

std::shared_ptr<PromOps::state11>
PromOps::execute_wpm11(std::shared_ptr<PromOps::state11> s) {
  if (s->prom_enable11) {
    return std::make_shared<PromOps::state11>(state11{
        update_nth<unsigned int>(s->prom_addr11, s->prom_data11, s->rom11),
        s->prom_addr11, s->prom_data11, s->prom_enable11});
  } else {
    return s;
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
