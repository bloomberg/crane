#include "wf_fix_sigma_domain.h"

uint64_t WfFixSigmaDomain::sw(uint64_t a, uint64_t b) {
  return sw_crane_Fix_F<uint64_t>(sigma<uint64_t, uint64_t>{a, b});
}

uint64_t WfFixSigmaDomain::sw_unfold(uint64_t a, uint64_t b) {
  if (a <= 0) {
    return b;
  } else {
    uint64_t n = a - 1;
    return (sw(b, n) + 1);
  }
}

WfFixSigmaDomain::sw_graph WfFixSigmaDomain::sw_graph_correct(uint64_t a,
                                                              uint64_t b) {
  return sw_graph_correct_crane_Fix_F<WfFixSigmaDomain::sw_graph>(
      sigma<uint64_t, uint64_t>{a, b});
}
