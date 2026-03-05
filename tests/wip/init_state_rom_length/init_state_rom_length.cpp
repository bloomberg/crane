#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <init_state_rom_length.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<List<unsigned int>>
InitStateRomLength::rom(const std::shared_ptr<InitStateRomLength::state> &s) {
  return s->rom;
}
