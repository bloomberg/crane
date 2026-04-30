#include <load_program_head_write.h>

List<unsigned int> LoadProgramHeadWrite::update_nth(const unsigned int &n,
                                                    unsigned int x,
                                                    List<unsigned int> l) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v_mut())) {
      return l;
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(l.v_mut());
      return List<unsigned int>::cons(x, *(d_a1));
    }
  } else {
    unsigned int n_ = n - 1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v_mut())) {
      return l;
    } else {
      auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(l.v_mut());
      return List<unsigned int>::cons(d_a00, update_nth(n_, x, *(d_a10)));
    }
  }
}

LoadProgramHeadWrite::state
LoadProgramHeadWrite::set_prom_params(const LoadProgramHeadWrite::state &s,
                                      unsigned int addr, unsigned int data,
                                      bool enable) {
  return state{s.rom, addr, data, enable};
}

LoadProgramHeadWrite::state
LoadProgramHeadWrite::execute_wpm(const LoadProgramHeadWrite::state &s) {
  List<unsigned int> new_rom;
  if (s.prom_enable) {
    new_rom = update_nth(s.prom_addr, s.prom_data, s.rom);
  } else {
    new_rom = s.rom;
  }
  return state{new_rom, s.prom_addr, s.prom_data, s.prom_enable};
}

LoadProgramHeadWrite::state
LoadProgramHeadWrite::load_program(LoadProgramHeadWrite::state s,
                                   const unsigned int &base,
                                   const List<unsigned int> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(bytes.v())) {
    return s;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(bytes.v());
    LoadProgramHeadWrite::state s1 =
        set_prom_params(std::move(s), base, d_a0, true);
    LoadProgramHeadWrite::state s2 = execute_wpm(std::move(s1));
    return load_program(std::move(s2),
                        (4096u ? (base + 1u) % 4096u : (base + 1u)), *(d_a1));
  }
}
