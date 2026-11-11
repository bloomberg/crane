#include "eta_arg.h"

uint64_t EtaArg::cost(const List<uint64_t> &xs) {
  return eta_tick(xs.length());
}

uint64_t EtaArg::step(uint64_t k, uint64_t acc, uint64_t x) {
  return ((acc + x) + k);
}

uint64_t EtaArg::total(const List<uint64_t> &xs) {
  return xs.template fold_left<uint64_t>(
      [&]() {
        auto _pa0 = cost(xs);
        return [=](uint64_t _x0, uint64_t _x1) -> uint64_t {
          return step(_pa0, _x0, _x1);
        };
      }(),
      UINT64_C(0));
}
