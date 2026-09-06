#include "eta_fold_callback.h"

uint64_t EtaFoldCallback::grab(const EtaFoldCallback::box &b, uint64_t k) {
  const auto &[a0] = b;
  return a0.template fold_right<uint64_t>(
      [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }, k);
}
