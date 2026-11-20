#include "typed_mapping_interface_lib.h"

std::uint32_t Lib::double_(std::uint32_t m) {
  uint64_t n = static_cast<uint64_t>(m);
  return static_cast<std::uint32_t>((n + n));
}

uint64_t Lib::value(std::uint32_t m) {
  uint64_t n = static_cast<uint64_t>(m);
  return n;
}
