#pragma once

#include <cstdint>

struct NestedRecordUpdateQual {
  struct Shadow {
    uint64_t value;
  };

  static Shadow bump(const Shadow &x);
  static inline const Shadow t = bump(Shadow{UINT64_C(1)});
};
