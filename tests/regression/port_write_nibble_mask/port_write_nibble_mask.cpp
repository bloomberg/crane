#include <port_write_nibble_mask.h>

unsigned int PortWriteNibbleMask::nibble_of_nat(const unsigned int &n) {
  return (16u ? n % 16u : n);
}

PortWriteNibbleMask::ram_chip
PortWriteNibbleMask::upd_port_in_chip(const PortWriteNibbleMask::ram_chip &,
                                      const unsigned int &v) {
  return ram_chip{nibble_of_nat(v)};
}
