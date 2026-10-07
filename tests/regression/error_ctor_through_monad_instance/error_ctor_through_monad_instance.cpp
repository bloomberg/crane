#include "error_ctor_through_monad_instance.h"

Bool0 PeanoNat::eqb(const Nat &n, const Nat &m) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return Bool0::TRUE_;
    } else {
      return Bool0::FALSE_;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    if (std::holds_alternative<typename Nat::O>(m.v())) {
      return Bool0::FALSE_;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(m.v());
      return PeanoNat::eqb(*a0, *a00);
    }
  }
}

EOU<Dv> ErrorCtorThroughMonadInstance::eval_icmp(const Nat &x, const Nat &y) {
  return EOU_monad::template bind<Bool0, Dv>(
      [&]() {
        switch (PeanoNat::eqb(x, y)) {
        case Bool0::TRUE_: {
          return EOU_monad::template ret<Bool0>(Bool0::TRUE_);
        }
        case Bool0::FALSE_: {
          return EOU<Bool0>::err(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
        }
        default:
          std::unreachable();
        }
      }(),
      [](Bool0 b) { return EOU_monad::template ret<Dv>(Dv::dvbool(b)); });
}
