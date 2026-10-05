#include "signature_parity_fix.h"

uint64_t SignatureParityFix::f(uint64_t seed) {
  {
    uint64_t _lc1_n = (seed + 1);
    uint64_t _lc1_loop_n = std::move(_lc1_n);
    while (true) {
      if (_lc1_loop_n <= 0) {
        return seed;
      } else {
        uint64_t n_ = _lc1_loop_n - 1;
        _lc1_loop_n = n_;
      }
    }
  }
}
