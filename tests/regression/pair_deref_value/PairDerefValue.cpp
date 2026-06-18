#include "PairDerefValue.h"

#include "Datatypes.h"

namespace PairDerefValue {

bool NatKey::key_eq_dec(const Datatypes::Nat &n, const Datatypes::Nat &x0) {
  if (std::holds_alternative<typename Datatypes::Nat::O>(n.v())) {
    if (std::holds_alternative<typename Datatypes::Nat::O>(x0.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Datatypes::Nat::S>(n.v());
    if (std::holds_alternative<typename Datatypes::Nat::O>(x0.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Datatypes::Nat::S>(x0.v());
      if (key_eq_dec(*a0, *a00)) {
        return true;
      } else {
        return false;
      }
    }
  }
}

} // namespace PairDerefValue
