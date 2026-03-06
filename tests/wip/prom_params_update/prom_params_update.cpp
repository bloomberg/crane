#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <prom_params_update.h>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int
PromParamsUpdate::acc(const std::shared_ptr<PromParamsUpdate::state> &s) {
  return s->acc;
}

std::shared_ptr<List<unsigned int>>
PromParamsUpdate::regs(const std::shared_ptr<PromParamsUpdate::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>>
PromParamsUpdate::rom(const std::shared_ptr<PromParamsUpdate::state> &s) {
  return s->rom;
}

unsigned int
PromParamsUpdate::prom_addr(const std::shared_ptr<PromParamsUpdate::state> &s) {
  return s->prom_addr;
}

unsigned int
PromParamsUpdate::prom_data(const std::shared_ptr<PromParamsUpdate::state> &s) {
  return s->prom_data;
}

bool PromParamsUpdate::prom_enable(
    const std::shared_ptr<PromParamsUpdate::state> &s) {
  return s->prom_enable;
}

std::shared_ptr<PromParamsUpdate::state>
PromParamsUpdate::set_prom_params(std::shared_ptr<PromParamsUpdate::state> s,
                                  const unsigned int addr,
                                  const unsigned int data, const bool enable) {
  return std::make_shared<PromParamsUpdate::state>(
      state{s->acc, s->regs, s->rom, std::move(addr), std::move(data),
            std::move(enable)});
}
