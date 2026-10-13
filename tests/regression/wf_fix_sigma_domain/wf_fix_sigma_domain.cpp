#include "wf_fix_sigma_domain.h"

uint64_t WfFixSigmaDomain::sw(uint64_t a, uint64_t b) {
  auto fix_F_impl = [](auto &_self_fix_F,
                       sigma<uint64_t, uint64_t> x) -> uint64_t {
    return sw_functional(x.pr1, x.pr2, [=](uint64_t a0, uint64_t b0) {
      sigma<uint64_t, uint64_t> y = sigma<uint64_t, uint64_t>{a0, b0};
      return _self_fix_F(_self_fix_F, y);
    });
  };
  {
    sigma<uint64_t, uint64_t> _lc1_x = sigma<uint64_t, uint64_t>{a, b};
    return fix_F_impl(fix_F_impl, std::move(_lc1_x));
  }
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
  auto fix_F_impl =
      [](auto &_self_fix_F,
         sigma<uint64_t, uint64_t> x) -> WfFixSigmaDomain::sw_graph {
    uint64_t x0 = x.pr2;
    crane::fn<WfFixSigmaDomain::sw_graph(uint64_t, uint64_t)> h =
        [=](uint64_t a0, uint64_t b0) {
          sigma<uint64_t, uint64_t> y = sigma<uint64_t, uint64_t>{a0, b0};
          return _self_fix_F(_self_fix_F, y);
        };
    if (x.pr1 <= 0) {
      return sw_graph::sw_graph_equation_1(x0);
    } else {
      uint64_t n = x.pr1 - 1;
      return sw_graph::sw_graph_equation_2(n, x0, h(x0, n));
    }
  };
  {
    sigma<uint64_t, uint64_t> _lc1_x = sigma<uint64_t, uint64_t>{a, b};
    return fix_F_impl(fix_F_impl, std::move(_lc1_x));
  }
}
