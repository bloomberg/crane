#include "prom_ops.h"

bool PromOps::nat_list_eqb(const List<uint64_t> &xs, const List<uint64_t> &ys) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
    if (std::holds_alternative<typename List<uint64_t>::Nil>(ys.v())) {
      return false;
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(ys.v());
      return (a0 == a00 && nat_list_eqb(*a1, *a10));
    }
  }
}

uint64_t PromOps::prom_data_or_zero(const PromOps::state1 &s) {
  if (s.prom_enable1) {
    return s.prom_data1;
  } else {
    return UINT64_C(0);
  }
}

uint64_t PromOps::flagged_sum(const PromOps::state2 &s) {
  return ((s.acc2 + s.prom_addr2) +
          (s.prom_enable2 ? s.prom_data2 : UINT64_C(0)));
}

PromOps::state3 PromOps::set_prom_params3(const PromOps::state3 &s,
                                          uint64_t addr, uint64_t data,
                                          bool enable) {
  return state3{s.acc3,     s.regs3,     s.carry3,   s.pc3,        s.stack3,
                s.ram_sys3, s.cur_bank3, s.sel_ram3, s.rom_ports3, s.sel_rom3,
                s.rom3,     s.test_pin3, addr,       data,         enable};
}

PromOps::state5 PromOps::set_prom_params5(const PromOps::state5 &s,
                                          uint64_t addr, uint64_t data,
                                          bool enable) {
  return state5{s.acc5, s.regs5, s.rom5, addr, data, enable};
}

PromOps::state6 PromOps::set_prom_params6(const PromOps::state6 &s,
                                          uint64_t addr, uint64_t data,
                                          bool enable) {
  return state6{s.rom6, addr, data, enable};
}

PromOps::state7 PromOps::set_prom_params7(const PromOps::state7 &s,
                                          uint64_t addr, uint64_t data,
                                          bool enable) {
  return state7{s.regs7, s.ram_sys7, addr, data, enable};
}

PromOps::state8 PromOps::set_prom_params8(const PromOps::state8 &s,
                                          uint64_t addr, uint64_t data,
                                          bool enable) {
  return state8{s.regs8, s.ram_sys8, addr, data, enable};
}

PromOps::state9 PromOps::set_prom_params9(const PromOps::state9 &s,
                                          uint64_t addr, uint64_t data,
                                          bool enable) {
  return state9{s.rom9, addr, data, enable};
}

PromOps::state10 PromOps::set_prom_params10(const PromOps::state10 &s,
                                            uint64_t addr, uint64_t data,
                                            bool enable) {
  return state10{s.regs10,  s.rom10,      s.acc10,       s.pc10,
                 s.stack10, s.cur_bank10, s.rom_ports10, s.sel_rom10,
                 addr,      data,         enable};
}

PromOps::state10 PromOps::execute_wpm10(const PromOps::state10 &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable10) {
    new_rom = update_nth<uint64_t>(s.prom_addr10, s.prom_data10, s.rom10);
  } else {
    new_rom = s.rom10;
  }
  return state10{s.regs10,      new_rom,       s.acc10,        s.pc10,
                 s.stack10,     s.cur_bank10,  s.rom_ports10,  s.sel_rom10,
                 s.prom_addr10, s.prom_data10, s.prom_enable10};
}

PromOps::state11 PromOps::execute_wpm11(PromOps::state11 s) {
  if (s.prom_enable11) {
    return state11{update_nth<uint64_t>(s.prom_addr11, s.prom_data11, s.rom11),
                   s.prom_addr11, s.prom_data11, s.prom_enable11};
  } else {
    return s;
  }
}

bool Bool::eqb(bool b1, bool b2) {
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
