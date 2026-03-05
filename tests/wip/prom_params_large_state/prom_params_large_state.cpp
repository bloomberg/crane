#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prom_params_large_state.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int PromParamsLargeState::acc(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> PromParamsLargeState::regs(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->regs;
}

bool PromParamsLargeState::carry(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->carry;
}

unsigned int PromParamsLargeState::pc(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> PromParamsLargeState::stack(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->stack;
}

std::shared_ptr<List<unsigned int>> PromParamsLargeState::ram_sys(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->ram_sys;
}

unsigned int PromParamsLargeState::cur_bank(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->cur_bank;
}

unsigned int PromParamsLargeState::sel_ram(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->sel_ram;
}

std::shared_ptr<List<unsigned int>> PromParamsLargeState::rom_ports(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->rom_ports;
}

unsigned int PromParamsLargeState::sel_rom(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->sel_rom;
}

std::shared_ptr<List<unsigned int>> PromParamsLargeState::rom(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->rom;
}

bool PromParamsLargeState::test_pin(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->test_pin;
}

unsigned int PromParamsLargeState::prom_addr(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->prom_addr;
}

unsigned int PromParamsLargeState::prom_data(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->prom_data;
}

bool PromParamsLargeState::prom_enable(
    const std::shared_ptr<PromParamsLargeState::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<PromParamsLargeState::state>
PromParamsLargeState::set_prom_params(
    std::shared_ptr<PromParamsLargeState::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<PromParamsLargeState::state>(
      state{s->acc, s->regs, s->carry, s->pc, s->stack, s->ram_sys, s->cur_bank,
            s->sel_ram, s->rom_ports, s->sel_rom, s->rom, s->test_pin,
            std::move(addr), std::move(data), std::move(enable)});
}
