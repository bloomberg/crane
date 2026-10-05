#include "wrr_preserves_other_ports.h"

WrrPreservesOtherPorts::state
WrrPreservesOtherPorts::execute_wrr(const WrrPreservesOtherPorts::state &s) {
  return state{
      s.acc,
      update_nth<uint64_t>(s.sel_rom, (s.acc % UINT64_C(16)), s.rom_ports),
      s.sel_rom};
}
