#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <init_state_register_count.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> InitStateRegisterCount::regs(
    const std::shared_ptr<InitStateRegisterCount::state> &s) {
  return s->regs;
}

std::shared_ptr<List<unsigned int>> InitStateRegisterCount::rom(
    const std::shared_ptr<InitStateRegisterCount::state> &s) {
  return s->rom;
}
