#include <algorithm>
#include <any>
#include <cassert>
#include <decode_inc_wf_edge_0061.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
DecodeIncWfEdge0061::acc(const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> DecodeIncWfEdge0061::regs(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->regs;
}

bool DecodeIncWfEdge0061::carry(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->carry;
}

unsigned int
DecodeIncWfEdge0061::pc(const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> DecodeIncWfEdge0061::stack(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->stack;
}

std::shared_ptr<List<unsigned int>> DecodeIncWfEdge0061::ram_sys(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->ram_sys;
}

unsigned int DecodeIncWfEdge0061::cur_bank(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->cur_bank;
}

unsigned int DecodeIncWfEdge0061::sel_ram(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->sel_ram;
}

std::shared_ptr<List<unsigned int>> DecodeIncWfEdge0061::rom_ports(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->rom_ports;
}

unsigned int DecodeIncWfEdge0061::sel_rom(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->sel_rom;
}

std::shared_ptr<List<unsigned int>>
DecodeIncWfEdge0061::rom(const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->rom;
}

bool DecodeIncWfEdge0061::test_pin(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->test_pin;
}

unsigned int DecodeIncWfEdge0061::prom_addr(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->prom_addr;
}

unsigned int DecodeIncWfEdge0061::prom_data(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->prom_data;
}

bool DecodeIncWfEdge0061::prom_enable(
    const std::shared_ptr<DecodeIncWfEdge0061::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<DecodeIncWfEdge0061::state>
DecodeIncWfEdge0061::set_prom_params(
    std::shared_ptr<DecodeIncWfEdge0061::state> s, const unsigned int addr,
    const unsigned int data, const bool enable) {
  return std::make_shared<DecodeIncWfEdge0061::state>(
      state{s->acc, s->regs, s->carry, s->pc, s->stack, s->ram_sys, s->cur_bank,
            s->sel_ram, s->rom_ports, s->sel_rom, s->rom, s->test_pin,
            std::move(addr), std::move(data), std::move(enable)});
}
