#include "option_deep_drain.h"

OptionDeepDrain::chain OptionDeepDrain::build(uint64_t n,
                                              OptionDeepDrain::chain acc) {
  OptionDeepDrain::chain _loop_acc = std::move(acc);
  uint64_t _loop_n = std::move(n);
  while (true) {
    if (_loop_n <= 0) {
      return _loop_acc;
    } else {
      uint64_t m = _loop_n - 1;
      uint64_t _next_n = m;
      _loop_acc = chain::link(
          _loop_n,
          std::make_optional<OptionDeepDrain::chain>(std::move(_loop_acc)));
      _loop_n = _next_n;
    }
  }
}

uint64_t OptionDeepDrain::go(uint64_t n) {
  auto &&_sv = build(
      n, chain::link(UINT64_C(0), std::optional<OptionDeepDrain::chain>()));
  const auto &[a0, a1] =
      std::get<typename OptionDeepDrain::chain::Link>(_sv.v());
  return a0;
}
