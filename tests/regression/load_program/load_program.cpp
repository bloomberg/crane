#include <load_program.h>

LoadProgram::state LoadProgram::set_prom_params(const LoadProgram::state &s,
                                                unsigned int addr,
                                                unsigned int data,
                                                bool enable) {
  return state{s.rom, addr, data, enable};
}

LoadProgram::state LoadProgram::execute_wpm(const LoadProgram::state &s) {
  List<unsigned int> new_rom;
  if (s.prom_enable) {
    new_rom = update_nth<unsigned int>(s.prom_addr, s.prom_data, s.rom);
  } else {
    new_rom = s.rom;
  }
  return state{new_rom, s.prom_addr, s.prom_data, s.prom_enable};
}

LoadProgram::state LoadProgram::load_program(LoadProgram::state s,
                                             const unsigned int &base,
                                             const List<unsigned int> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(bytes.v())) {
    return s;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(bytes.v());
    LoadProgram::state s_ = set_prom_params(std::move(s), base, d_a0, true);
    LoadProgram::state s__ = execute_wpm(std::move(s_));
    return load_program(std::move(s__), (base + 1u), *(d_a1));
  }
}

LoadProgram::state_extended
LoadProgram::set_prom_params_ext(const LoadProgram::state_extended &s,
                                 unsigned int addr, unsigned int data,
                                 bool enable) {
  return state_extended{s.regs_len, s.rom_ext, s.pc,  s.stack_len,
                        addr,       data,      enable};
}

LoadProgram::state_extended
LoadProgram::execute_wpm_ext(const LoadProgram::state_extended &s) {
  List<unsigned int> new_rom;
  if (s.prom_enable_ext) {
    new_rom =
        update_nth<unsigned int>(s.prom_addr_ext, s.prom_data_ext, s.rom_ext);
  } else {
    new_rom = s.rom_ext;
  }
  return state_extended{s.regs_len,       new_rom,         s.pc,
                        s.stack_len,      s.prom_addr_ext, s.prom_data_ext,
                        s.prom_enable_ext};
}

LoadProgram::state_simple
LoadProgram::write_byte(const LoadProgram::state_simple &s,
                        const unsigned int &b) {
  return state_simple{update_nth<unsigned int>(s.ptr_, b, s.rom_),
                      (s.ptr_ + 1)};
}

LoadProgram::state_simple
LoadProgram::load_program_simple(LoadProgram::state_simple s,
                                 const List<unsigned int> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(bytes.v())) {
    return s;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(bytes.v());
    return load_program_simple(write_byte(std::move(s), d_a0), *(d_a1));
  }
}
