#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_prom_then_wpm.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<SetPromThenWpm::state>
SetPromThenWpm::set_prom_params(std::shared_ptr<SetPromThenWpm::state> s,
                                const unsigned int addr,
                                const unsigned int data, const bool enable) {
  return std::make_shared<SetPromThenWpm::state>(
      state{s->regs, s->rom, s->acc, s->pc, s->stack, s->cur_bank, s->rom_ports,
            s->sel_rom, std::move(addr), std::move(data), std::move(enable)});
}

std::shared_ptr<SetPromThenWpm::state>
SetPromThenWpm::execute_wpm(std::shared_ptr<SetPromThenWpm::state> s) {
  std::shared_ptr<List<unsigned int>> new_rom;
  if (s->prom_enable) {
    new_rom = update_nth<unsigned int>(s->prom_addr, s->prom_data, s->rom);
  } else {
    new_rom = std::move(s)->rom;
  }
  return std::make_shared<SetPromThenWpm::state>(state{
      s->regs, std::move(new_rom), s->acc, s->pc, s->stack, s->cur_bank,
      s->rom_ports, s->sel_rom, s->prom_addr, s->prom_data, s->prom_enable});
}
