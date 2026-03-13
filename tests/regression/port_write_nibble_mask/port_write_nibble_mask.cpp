#include <port_write_nibble_mask.h>

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

__attribute__((pure)) unsigned int
PortWriteNibbleMask::nibble_of_nat(const unsigned int n) {
  return (n % 16u);
}

std::shared_ptr<PortWriteNibbleMask::ram_chip>
PortWriteNibbleMask::upd_port_in_chip(
    const std::shared_ptr<PortWriteNibbleMask::ram_chip> &_x,
    const unsigned int v) {
  return std::make_shared<PortWriteNibbleMask::ram_chip>(
      ram_chip{nibble_of_nat(std::move(v))});
}
