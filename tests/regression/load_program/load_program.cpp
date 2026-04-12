#include <load_program.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<LoadProgram::state>
LoadProgram::set_prom_params(const std::shared_ptr<LoadProgram::state> &s,
                             const unsigned int addr, const unsigned int data,
                             const bool enable) {
  return std::make_shared<LoadProgram::state>(
      state{s->rom, addr, data, enable});
}

std::shared_ptr<LoadProgram::state>
LoadProgram::execute_wpm(const std::shared_ptr<LoadProgram::state> &s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = s->rom;
  }
  return std::make_shared<LoadProgram::state>(
      state{new_rom, s->prom_addr, s->prom_data, s->prom_enable});
}

std::shared_ptr<LoadProgram::state>
LoadProgram::load_program(std::shared_ptr<LoadProgram::state> s,
                          const unsigned int base,
                          const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{[&](const typename List<unsigned int>::Nil)
                     -> std::shared_ptr<LoadProgram::state> { return s; },
                 [&](const typename List<unsigned int>::Cons _args)
                     -> std::shared_ptr<LoadProgram::state> {
                   std::shared_ptr<LoadProgram::state> s_ =
                       set_prom_params(std::move(s), base, _args.d_a0, true);
                   std::shared_ptr<LoadProgram::state> s__ =
                       execute_wpm(std::move(s_));
                   return load_program(std::move(s__), (base + 1u), _args.d_a1);
                 }},
      bytes->v());
}

std::shared_ptr<LoadProgram::state_extended> LoadProgram::set_prom_params_ext(
    const std::shared_ptr<LoadProgram::state_extended> &s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<LoadProgram::state_extended>(state_extended{
      s->regs_len, s->rom_ext, s->pc, s->stack_len, addr, data, enable});
}

std::shared_ptr<LoadProgram::state_extended> LoadProgram::execute_wpm_ext(
    const std::shared_ptr<LoadProgram::state_extended> &s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable_ext) {
    new_rom = update_nth<unsigned int>(s->prom_addr_ext, s->prom_data_ext,
                                       s->rom_ext);
  } else {
    new_rom = s->rom_ext;
  }
  return std::make_shared<LoadProgram::state_extended>(
      state_extended{s->regs_len, new_rom, s->pc, s->stack_len,
                     s->prom_addr_ext, s->prom_data_ext, s->prom_enable_ext});
}

std::shared_ptr<LoadProgram::state_simple>
LoadProgram::write_byte(const std::shared_ptr<LoadProgram::state_simple> &s,
                        const unsigned int b) {
  return std::make_shared<LoadProgram::state_simple>(state_simple{
      update_nth<unsigned int>(s->ptr_, b, s->rom_), (s->ptr_ + 1)});
}

std::shared_ptr<LoadProgram::state_simple> LoadProgram::load_program_simple(
    std::shared_ptr<LoadProgram::state_simple> s,
    const std::shared_ptr<List<unsigned int>> &bytes) {
  return std::visit(
      Overloaded{
          [&](const typename List<unsigned int>::Nil)
              -> std::shared_ptr<LoadProgram::state_simple> { return s; },
          [&](const typename List<unsigned int>::Cons _args)
              -> std::shared_ptr<LoadProgram::state_simple> {
            return load_program_simple(write_byte(std::move(s), _args.d_a0),
                                       _args.d_a1);
          }},
      bytes->v());
}
