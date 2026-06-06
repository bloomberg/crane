#ifndef INCLUDED_JMS_BBL_ROUNDTRIP
#define INCLUDED_JMS_BBL_ROUNDTRIP

#include <utility>

struct JmsBblRoundtrip {
  struct state {
    uint64_t pc;
    uint64_t ret;
    bool has_ret;
  };

  static uint64_t addr12_of_nat(uint64_t n);
  static state execute_jms(const state &s, uint64_t addr);
  static state execute_bbl(state s);
  static inline const state sample = state{UINT64_C(100), UINT64_C(0), false};
  static inline const bool t =
      execute_bbl(execute_jms(sample, UINT64_C(200))).pc == UINT64_C(102);
};

#endif // INCLUDED_JMS_BBL_ROUNDTRIP
