#include <prom_ops.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool PromOps::nat_list_eqb(const List<unsigned int> &xs,
                                                 const List<unsigned int> &ys) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(xs.v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(ys.v())) {
      return false;
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(ys.v());
      return (d_a0 == d_a00 && nat_list_eqb(*(d_a1), *(d_a10)));
    }
  }
}

__attribute__((pure)) unsigned int
PromOps::prom_data_or_zero(const PromOps::state1 &s) {
  if (s.prom_enable1) {
    return s.prom_data1;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int
PromOps::flagged_sum(const PromOps::state2 &s) {
  return ((s.acc2 + s.prom_addr2) + [=]() mutable -> unsigned int {
    if (s.prom_enable2) {
      return s.prom_data2;
    } else {
      return 0u;
    }
  }());
}

__attribute__((pure)) PromOps::state3
PromOps::set_prom_params3(const PromOps::state3 &s, unsigned int addr,
                          unsigned int data, bool enable) {
  return state3{s.acc3,     s.regs3,     s.carry3,   s.pc3,        s.stack3,
                s.ram_sys3, s.cur_bank3, s.sel_ram3, s.rom_ports3, s.sel_rom3,
                s.rom3,     s.test_pin3, addr,       data,         enable};
}

__attribute__((pure)) PromOps::state5
PromOps::set_prom_params5(const PromOps::state5 &s, unsigned int addr,
                          unsigned int data, bool enable) {
  return state5{s.acc5, s.regs5, s.rom5, addr, data, enable};
}

__attribute__((pure)) PromOps::state6
PromOps::set_prom_params6(const PromOps::state6 &s, unsigned int addr,
                          unsigned int data, bool enable) {
  return state6{s.rom6, addr, data, enable};
}

__attribute__((pure)) PromOps::state7
PromOps::set_prom_params7(const PromOps::state7 &s, unsigned int addr,
                          unsigned int data, bool enable) {
  return state7{s.regs7, s.ram_sys7, addr, data, enable};
}

__attribute__((pure)) PromOps::state8
PromOps::set_prom_params8(const PromOps::state8 &s, unsigned int addr,
                          unsigned int data, bool enable) {
  return state8{s.regs8, s.ram_sys8, addr, data, enable};
}

__attribute__((pure)) PromOps::state9
PromOps::set_prom_params9(const PromOps::state9 &s, unsigned int addr,
                          unsigned int data, bool enable) {
  return state9{s.rom9, addr, data, enable};
}

__attribute__((pure)) PromOps::state10
PromOps::set_prom_params10(const PromOps::state10 &s, unsigned int addr,
                           unsigned int data, bool enable) {
  return state10{s.regs10,  s.rom10,      s.acc10,       s.pc10,
                 s.stack10, s.cur_bank10, s.rom_ports10, s.sel_rom10,
                 addr,      data,         enable};
}

__attribute__((pure)) PromOps::state10
PromOps::execute_wpm10(const PromOps::state10 &s) {
  List<unsigned int> new_rom;
  if (s.prom_enable10) {
    new_rom = update_nth<unsigned int>(s.prom_addr10, s.prom_data10, s.rom10);
  } else {
    new_rom = s.rom10;
  }
  return state10{s.regs10,      new_rom,       s.acc10,        s.pc10,
                 s.stack10,     s.cur_bank10,  s.rom_ports10,  s.sel_rom10,
                 s.prom_addr10, s.prom_data10, s.prom_enable10};
}

__attribute__((pure)) PromOps::state11
PromOps::execute_wpm11(PromOps::state11 s) {
  if (s.prom_enable11) {
    return state11{
        update_nth<unsigned int>(s.prom_addr11, s.prom_data11, s.rom11),
        s.prom_addr11, s.prom_data11, s.prom_enable11};
  } else {
    return s;
  }
}

__attribute__((pure)) bool Bool::eqb(const bool &b1, const bool &b2) {
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
