#include <algorithm>
#include <any>
#include <cassert>
#include <encode_decode_canonical_edge_0029.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int EncodeDecodeCanonicalEdge0029::acc(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>> EncodeDecodeCanonicalEdge0029::regs(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->regs;
}

bool EncodeDecodeCanonicalEdge0029::carry(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->carry;
}

unsigned int EncodeDecodeCanonicalEdge0029::pc(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->pc;
}

std::shared_ptr<List<unsigned int>> EncodeDecodeCanonicalEdge0029::stack(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->stack;
}

std::shared_ptr<List<unsigned int>> EncodeDecodeCanonicalEdge0029::ram_sys(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->ram_sys;
}

unsigned int EncodeDecodeCanonicalEdge0029::cur_bank(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->cur_bank;
}

unsigned int EncodeDecodeCanonicalEdge0029::sel_ram(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->sel_ram;
}

std::shared_ptr<List<unsigned int>> EncodeDecodeCanonicalEdge0029::rom_ports(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->rom_ports;
}

unsigned int EncodeDecodeCanonicalEdge0029::sel_rom(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->sel_rom;
}

std::shared_ptr<List<unsigned int>> EncodeDecodeCanonicalEdge0029::rom(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->rom;
}

bool EncodeDecodeCanonicalEdge0029::test_pin(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->test_pin;
}

unsigned int EncodeDecodeCanonicalEdge0029::prom_addr(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->prom_addr;
}

unsigned int EncodeDecodeCanonicalEdge0029::prom_data(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->prom_data;
}

bool EncodeDecodeCanonicalEdge0029::prom_enable(
    const std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<EncodeDecodeCanonicalEdge0029::state>
EncodeDecodeCanonicalEdge0029::set_prom_params(
    std::shared_ptr<EncodeDecodeCanonicalEdge0029::state> s,
    const unsigned int addr, const unsigned int data, const bool enable) {
  return std::make_shared<EncodeDecodeCanonicalEdge0029::state>(
      state{s->acc, s->regs, s->carry, s->pc, s->stack, s->ram_sys, s->cur_bank,
            s->sel_ram, s->rom_ports, s->sel_rom, s->rom, s->test_pin,
            std::move(addr), std::move(data), std::move(enable)});
}
