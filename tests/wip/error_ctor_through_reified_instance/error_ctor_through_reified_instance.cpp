#include "error_ctor_through_reified_instance.h"

bool PeanoNat::eqb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return true;
    } else {
      return false;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return false;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::eqb(*a0, *a00);
    }
  }
}

EOU<Dv> ErrorCtorThroughReifiedInstance::eval_icmp(const Nat &x, const Nat &y) {
  return EOU_monad::template bind<bool, Dv>(
      (PeanoNat::eqb(x, y) ? EOU_monad::template ret<bool>(true)
                           : EOU<Dv>::err(Nat::s(Nat::s(Nat::s(
                                 Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))),
      [](bool b) { return EOU_monad::template ret<Dv>(Dv::dvbool(b)); });
}
