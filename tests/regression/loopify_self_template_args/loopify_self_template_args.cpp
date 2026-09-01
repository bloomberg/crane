#include "loopify_self_template_args.h"

bool PeanoNat::eq_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      uint64_t _x = m - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      bool s = PeanoNat::eq_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

List::list<uint64_t>
LoopifySelfTemplateArgs::rm(const List::list<uint64_t> &l) {
  return List::template remove<uint64_t>(PeanoNat::eq_dec, UINT64_C(2), l);
}
