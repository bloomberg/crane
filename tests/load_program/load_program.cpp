#include "load_program.h"

LoadProgram::state LoadProgram::set_prom_params(const LoadProgram::state &s,
                                                uint64_t addr, uint64_t data,
                                                bool enable) {
  return state{s.rom, addr, data, enable};
}

LoadProgram::state LoadProgram::execute_wpm(const LoadProgram::state &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable) {
    new_rom = update_nth<uint64_t>(s.prom_addr, s.prom_data, s.rom);
  } else {
    new_rom = s.rom;
  }
  return state{new_rom, s.prom_addr, s.prom_data, s.prom_enable};
}

LoadProgram::state LoadProgram::load_program(LoadProgram::state s,
                                             uint64_t base,
                                             const List<uint64_t> &bytes) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(bytes.v())) {
    return s;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(bytes.v());
    LoadProgram::state s_ = set_prom_params(std::move(s), base, a0, true);
    LoadProgram::state s__ = execute_wpm(std::move(s_));
    return load_program(std::move(s__), (base + UINT64_C(1)), *a1);
  }
}

LoadProgram::state_extended
LoadProgram::set_prom_params_ext(const LoadProgram::state_extended &s,
                                 uint64_t addr, uint64_t data, bool enable) {
  return state_extended{s.regs_len, s.rom_ext, s.pc,  s.stack_len,
                        addr,       data,      enable};
}

LoadProgram::state_extended
LoadProgram::execute_wpm_ext(const LoadProgram::state_extended &s) {
  List<uint64_t> new_rom;
  if (s.prom_enable_ext) {
    new_rom = update_nth<uint64_t>(s.prom_addr_ext, s.prom_data_ext, s.rom_ext);
  } else {
    new_rom = s.rom_ext;
  }
  return state_extended{s.regs_len,       new_rom,         s.pc,
                        s.stack_len,      s.prom_addr_ext, s.prom_data_ext,
                        s.prom_enable_ext};
}

LoadProgram::state_simple
LoadProgram::write_byte(const LoadProgram::state_simple &s, uint64_t b) {
  return state_simple{update_nth<uint64_t>(s.ptr_, b, s.rom_), (s.ptr_ + 1)};
}

LoadProgram::state_simple
LoadProgram::load_program_simple(LoadProgram::state_simple s,
                                 const List<uint64_t> &bytes) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(bytes.v())) {
    return s;
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(bytes.v());
    return load_program_simple(write_byte(std::move(s), a0), *a1);
  }
}
