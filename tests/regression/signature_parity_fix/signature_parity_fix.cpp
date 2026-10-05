#include "signature_parity_fix.h"

uint64_t SignatureParityFix::f(uint64_t seed) {
  auto aux = [&](uint64_t n) -> uint64_t {
    uint64_t _loop_n = std::move(n);
    while (true) {
      if (_loop_n <= 0) {
        return seed;
      } else {
        uint64_t n_ = _loop_n - 1;
        _loop_n = n_;
      }
    }
  };
  return aux((seed + 1));
}
