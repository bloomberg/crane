#pragma once

#include <cstdint>
#include <typed_mapping_interface_lib.h>

struct Use {
  static std::uint32_t quad(std::uint32_t m);
  static inline const uint64_t answer =
      Lib::value(quad(static_cast<std::uint32_t>(UINT64_C(3))));
};
