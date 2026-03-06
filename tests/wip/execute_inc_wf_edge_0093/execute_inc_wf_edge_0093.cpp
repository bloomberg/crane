#include <algorithm>
#include <any>
#include <cassert>
#include <execute_inc_wf_edge_0093.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int ExecuteIncWfEdge0093::acc(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> ExecuteIncWfEdge0093::regs(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->regs;
}

bool ExecuteIncWfEdge0093::carry(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->carry;
}

unsigned int ExecuteIncWfEdge0093::pc(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> ExecuteIncWfEdge0093::stack(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->stack;
}

std::shared_ptr<List<unsigned int>> ExecuteIncWfEdge0093::ram_sys(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->ram_sys;
}

unsigned int ExecuteIncWfEdge0093::cur_bank(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->cur_bank;
}

unsigned int ExecuteIncWfEdge0093::sel_ram(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->sel_ram;
}

std::shared_ptr<List<unsigned int>> ExecuteIncWfEdge0093::rom_ports(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->rom_ports;
}

unsigned int ExecuteIncWfEdge0093::sel_rom(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->sel_rom;
}

std::shared_ptr<List<unsigned int>> ExecuteIncWfEdge0093::rom(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->rom;
}

bool ExecuteIncWfEdge0093::test_pin(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->test_pin;
}

unsigned int ExecuteIncWfEdge0093::prom_addr(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->prom_addr;
}

unsigned int ExecuteIncWfEdge0093::prom_data(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->prom_data;
}

bool ExecuteIncWfEdge0093::prom_enable(
    const std::shared_ptr<ExecuteIncWfEdge0093::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<ExecuteIncWfEdge0093::state>
ExecuteIncWfEdge0093::set_prom_params(
    std::shared_ptr<ExecuteIncWfEdge0093::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<ExecuteIncWfEdge0093::state>(
      state{s->acc, s->regs, s->carry, s->pc, s->stack, s->ram_sys, s->cur_bank,
            s->sel_ram, s->rom_ports, s->sel_rom, s->rom, s->test_pin,
            std::move(addr), std::move(data), std::move(enable)});
}
