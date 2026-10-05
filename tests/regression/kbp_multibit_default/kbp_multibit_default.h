#ifndef INCLUDED_KBP_MULTIBIT_DEFAULT
#define INCLUDED_KBP_MULTIBIT_DEFAULT

#include <cstdint>

struct KbpMultibitDefault {
  struct state {
    uint64_t acc;
  };

  static state execute_kbp(const state &s);
  static inline const state sample = state{UINT64_C(3)};
  static constexpr bool t = true;
};

#endif // INCLUDED_KBP_MULTIBIT_DEFAULT
