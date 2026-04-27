#include <wrr_preserves_other_ports.h>

__attribute__((pure)) WrrPreservesOtherPorts::state
WrrPreservesOtherPorts::execute_wrr(const WrrPreservesOtherPorts::state &s) {
  return state{s.acc,
               update_nth<unsigned int>(s.sel_rom, (16u ? s.acc % 16u : s.acc),
                                        s.rom_ports),
               s.sel_rom};
}
