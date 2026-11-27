#include "regrouped_recovery_exponential.h"

uint64_t RegroupedRecoveryExponential::lvl(uint64_t d) {
  if (d <= 0) {
    return UINT64_C(1);
  } else {
    uint64_t d_ = d - 1;
    return twice<crane::fn<uint64_t(uint64_t)>>(
        [&]() {
          crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)> _rg =
              crane_any_cast<
                  crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>, uint64_t)>>(
                  Datatypes::id(crane_erase_fn([&]() {
                    uint64_t m = lvl(d_);
                    return [=](const crane::fn<uint64_t(uint64_t)> &c,
                               uint64_t n) { return c(n) + m; };
                  }())));
          return [=, _rg = std::move(_rg)](crane::fn<uint64_t(uint64_t)> _rg0_0) {
            return [=, _rg = _rg](uint64_t _rg1_0) {
              return _rg(_rg0_0, _rg1_0);
            };
          };
        }(),
        [](uint64_t n) { return n; })(UINT64_C(0));
  }
}

crane::obj Datatypes::id(crane::obj x) { return x; }
