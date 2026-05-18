#include "wpm_ops.h"

bool WpmOps::nat_list_eqb(const List<uint64_t> &xs, const List<uint64_t> &ys) {
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

WpmOps::state1 WpmOps::execute_wpm1(const WpmOps::state1 &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable1) {
    new_rom = update_nth<uint64_t>(s.prom_addr1, s.prom_data1, s.rom1);
  } else {
    new_rom = s.rom1;
  }
  return state1{new_rom, s.prom_addr1, s.prom_data1, s.prom_enable1};
}

WpmOps::state2 WpmOps::execute_wpm2(const WpmOps::state2 &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable2) {
    new_rom = update_nth<uint64_t>(s.prom_addr2, s.prom_data2, s.rom2);
  } else {
    new_rom = s.rom2;
  }
  return state2{s.ram_sys2, new_rom, s.prom_addr2, s.prom_data2,
                s.prom_enable2};
}

WpmOps::state3 WpmOps::execute_wpm3(const WpmOps::state3 &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable3) {
    new_rom = update_nth<uint64_t>(s.prom_addr3, s.prom_data3, s.rom3);
  } else {
    new_rom = s.rom3;
  }
  return state3{s.regs3, new_rom, s.prom_addr3, s.prom_data3, s.prom_enable3};
}

WpmOps::state4 WpmOps::execute_wpm4(const WpmOps::state4 &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable4) {
    new_rom = update_nth<uint64_t>(s.prom_addr4, s.prom_data4, s.rom4);
  } else {
    new_rom = s.rom4;
  }
  return state4{new_rom, s.prom_addr4, s.prom_data4, s.prom_enable4};
}

WpmOps::state5 WpmOps::execute_wpm5(const WpmOps::state5 &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable5) {
    new_rom = update_nth<uint64_t>(s.prom_addr5, s.prom_data5, s.rom5);
  } else {
    new_rom = s.rom5;
  }
  return state5{new_rom, s.prom_addr5, s.prom_data5, s.prom_enable5};
}

WpmOps::state6 WpmOps::execute_wpm6(const WpmOps::state6 &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable6) {
    new_rom = update_nth<uint64_t>(s.prom_addr6, s.prom_data6, s.rom6);
  } else {
    new_rom = s.rom6;
  }
  return state6{new_rom, s.prom_addr6, s.prom_data6, s.prom_enable6};
}
