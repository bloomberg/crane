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
  return Monad0::template bind<EOU_monad, Bool0, Dv>(
      [=]() mutable {
        switch (PeanoNat::eqb(x, y)) {
        case Bool0::TRUE_: {
          return Monad0::template ret<EOU_monad, Bool0>(Bool0::TRUE_);
        }
        case Bool0::FALSE_: {
          return EOU<Dv>::err(
              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))));
        }
        default:
          std::unreachable();
        }
      }(),
      [](Bool0 b) {
        return Monad0::template ret<EOU_monad, Dv>(Dv::dvbool(b));
      });
}
