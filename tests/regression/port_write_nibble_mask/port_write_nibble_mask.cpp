#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <port_write_nibble_mask.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int PortWriteNibbleMask::chip_port(
    const std::shared_ptr<PortWriteNibbleMask::ram_chip> &r) {
  return r->chip_port;
}

unsigned int PortWriteNibbleMask::nibble_of_nat(const unsigned int n) {
  return (
      n %
      ((((((((((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1) +
        1) +
       1));
}

std::shared_ptr<PortWriteNibbleMask::ram_chip>
PortWriteNibbleMask::upd_port_in_chip(
    const std::shared_ptr<PortWriteNibbleMask::ram_chip> &_x,
    const unsigned int v) {
  return std::make_shared<PortWriteNibbleMask::ram_chip>(
      ram_chip{nibble_of_nat(std::move(v))});
}
