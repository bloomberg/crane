#include "port_write_nibble_mask.h"

uint64_t PortWriteNibbleMask::nibble_of_nat(uint64_t n) {
  return (UINT64_C(16) ? n % UINT64_C(16) : n);
}

PortWriteNibbleMask::ram_chip
PortWriteNibbleMask::upd_port_in_chip(const PortWriteNibbleMask::ram_chip &,
                                      uint64_t v) {
  return ram_chip{nibble_of_nat(v)};
}
