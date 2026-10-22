#include "eta_extended_global_elaborated.h"

/// A global Core reaches unapplied, applied where it is translated.
///
/// fun _ no => length no is simplified to fun _ => length, and Core
/// elaboration records length as named there, applied to nothing.
/// Translation, generating the lambda at the two-argument type its callee
/// wants, gives it its no back and translates the call length no it
/// built: one Core elaboration did not reach with that many arguments, which
/// CRANE_CHECK_IR reported as a call Core elaboration never saw.
uint64_t EtaExtendedGlobalElaborated::count_odds(const List<uint64_t> &l) {
  return both(l, [](List<uint64_t>, const List<uint64_t> &eta0_) {
    return eta0_.length();
  });
}

uint64_t EtaExtendedGlobalElaborated::count_evens(const List<uint64_t> &l) {
  return both(l, [](const List<uint64_t> &yes, List<uint64_t>) {
    return yes.length();
  });
}

bool Nat::even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      uint64_t n_ = n0 - 1;
      return Nat::even(n_);
    }
  }
}

bool Nat::odd(uint64_t n) { return !(Nat::even(n)); }
