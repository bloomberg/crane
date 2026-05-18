#ifndef INCLUDED_PORT_WRITE_NIBBLE_MASK
#define INCLUDED_PORT_WRITE_NIBBLE_MASK

#include <utility>

struct PortWriteNibbleMask {
  struct ram_chip {
    uint64_t chip_port;

    // ACCESSORS
    ram_chip clone() const { return ram_chip{(*this).chip_port}; }
  };

  static uint64_t nibble_of_nat(uint64_t n);
  static ram_chip upd_port_in_chip(const ram_chip &_x, uint64_t v);
  static inline const uint64_t t =
      upd_port_in_chip(ram_chip{UINT64_C(0)}, UINT64_C(31)).chip_port;
};

#endif // INCLUDED_PORT_WRITE_NIBBLE_MASK
