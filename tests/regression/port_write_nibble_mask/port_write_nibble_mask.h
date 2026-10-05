#ifndef INCLUDED_PORT_WRITE_NIBBLE_MASK
#define INCLUDED_PORT_WRITE_NIBBLE_MASK

#include <cstdint>
#include <utility>

struct PortWriteNibbleMask {
  struct ram_chip {
    uint64_t chip_port;
  };

  static uint64_t nibble_of_nat(uint64_t n);
  static ram_chip upd_port_in_chip(const ram_chip &_x, uint64_t v);
  static constexpr uint64_t t = UINT64_C(15);
};

#endif // INCLUDED_PORT_WRITE_NIBBLE_MASK
