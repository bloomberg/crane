#include "Nat.h"

#include "Datatypes.h"

namespace Nat {

bool leb(const Datatypes::Nat &n, const Datatypes::Nat &m) {
  if (std::holds_alternative<typename Datatypes::Nat::O>(n.v())) {
    return true;
  } else {
    const auto &[a0] = std::get<typename Datatypes::Nat::S>(n.v());
    if (std::holds_alternative<typename Datatypes::Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Datatypes::Nat::S>(m.v());
      return leb(*a0, *a00);
    }
  }
}

} // namespace Nat
