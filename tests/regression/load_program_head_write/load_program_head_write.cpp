#include "load_program_head_write.h"

List<uint64_t> LoadProgramHeadWrite::update_nth(uint64_t n, uint64_t x,
                                                List<uint64_t> l) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return l;
    } else {
      auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
      return List<uint64_t>::cons(x, *a1);
    }
  } else {
    uint64_t n_ = n - 1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return l;
    } else {
      auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
      return List<uint64_t>::cons(std::move(a00), update_nth(n_, x, *a10));
    }
  }
}

LoadProgramHeadWrite::state
LoadProgramHeadWrite::set_prom_params(const LoadProgramHeadWrite::state &s,
                                      uint64_t addr, uint64_t data,
                                      bool enable) {
  return state{s.rom, addr, data, enable};
}

LoadProgramHeadWrite::state
LoadProgramHeadWrite::execute_wpm(const LoadProgramHeadWrite::state &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable) {
    new_rom = update_nth(s.prom_addr, s.prom_data, s.rom);
  } else {
    new_rom = s.rom;
  }
  return state{new_rom, s.prom_addr, s.prom_data, s.prom_enable};
}

LoadProgramHeadWrite::state
LoadProgramHeadWrite::load_program(LoadProgramHeadWrite::state s, uint64_t base,
                                   const List<uint64_t> &bytes) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(bytes.v())) {
    return s;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(bytes.v());
    LoadProgramHeadWrite::state s1 =
        set_prom_params(std::move(s), base, a0, true);
    LoadProgramHeadWrite::state s2 = execute_wpm(std::move(s1));
    return load_program(std::move(s2),
                        (UINT64_C(4096) ? (base + UINT64_C(1)) % UINT64_C(4096)
                                        : (base + UINT64_C(1))),
                        *a1);
  }
}
