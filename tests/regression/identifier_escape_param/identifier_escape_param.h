#pragma once

#include <cstdint>

struct IdentifierEscapeParam {
  static uint64_t id_from_param(uint64_t double0);
  static uint64_t add_one_from_param(uint64_t double0);
  static inline const uint64_t t = add_one_from_param(UINT64_C(6));
};
