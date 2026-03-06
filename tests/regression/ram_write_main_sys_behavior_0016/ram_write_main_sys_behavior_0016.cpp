#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <ram_write_main_sys_behavior_0016.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>> RamWriteMainSysBehavior0016::rom(
    const std::shared_ptr<RamWriteMainSysBehavior0016::state> &s) {
  return s->rom;
}

unsigned int RamWriteMainSysBehavior0016::fetch_byte(
    const std::shared_ptr<RamWriteMainSysBehavior0016::state> &s,
    const unsigned int addr) {
  return s->rom->nth(addr, 0);
}
