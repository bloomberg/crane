#include <wrr_preserves_other_ports.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<WrrPreservesOtherPorts::state>
WrrPreservesOtherPorts::execute_wrr(
    const std::shared_ptr<WrrPreservesOtherPorts::state> &s) {
  return std::make_shared<WrrPreservesOtherPorts::state>(
      state{s->acc,
            update_nth<unsigned int>(s->sel_rom, (16u ? s->acc % 16u : s->acc),
                                     s->rom_ports),
            s->sel_rom});
}
