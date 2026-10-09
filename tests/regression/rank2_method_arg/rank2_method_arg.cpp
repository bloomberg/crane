#include "rank2_method_arg.h"

uint64_t Rank2MethodArg::run(uint64_t k) {
  static const auto erased_fn =
      crane::immortal(crane_erase_fn([](const auto &x) { return x; }));
  return AI::app2(erased_fn, (k + UINT64_C(4)));
}
