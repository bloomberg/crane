#pragma once

#include <cstdint>

struct KbpMultibitDefault {
  struct state {
    uint64_t acc;
  };

  static state execute_kbp(const state &s);
  static inline const state sample = state{UINT64_C(3)};
  static inline const bool t = execute_kbp(sample).acc == UINT64_C(15);
};
