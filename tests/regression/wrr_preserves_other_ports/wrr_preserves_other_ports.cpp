#include <wrr_preserves_other_ports.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<WrrPreservesOtherPorts::state>
WrrPreservesOtherPorts::execute_wrr(
    std::shared_ptr<WrrPreservesOtherPorts::state> s) {
  return std::make_shared<WrrPreservesOtherPorts::state>(
      state{s->acc,
            update_nth<unsigned int>(s->sel_rom, (s->acc % 16u), s->rom_ports),
            s->sel_rom});
}
