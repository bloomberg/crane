#include "Nat.h"

#include "Datatypes.h"

namespace Nat {

Datatypes::Nat add(const Datatypes::Nat &n, Datatypes::Nat m) {
  if (std::holds_alternative<typename Datatypes::Nat::O>(n.v())) {
    return m;
  } else {
    const auto &[a0] = std::get<typename Datatypes::Nat::S>(n.v());
    return Datatypes::Nat::s(add(*a0, std::move(m)));
  }
}

bool eqb(const Datatypes::Nat &n, const Datatypes::Nat &m) {
  if (std::holds_alternative<typename Datatypes::Nat::O>(n.v())) {
    if (std::holds_alternative<typename Datatypes::Nat::O>(m.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Datatypes::Nat::S>(n.v());
    if (std::holds_alternative<typename Datatypes::Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Datatypes::Nat::S>(m.v());
      return eqb(*a0, *a00);
    }
  }
}

} // namespace Nat
