#ifndef INCLUDED_SEPEXTFUNCTORMODTYPEVIAAPPLICATION
#define INCLUDED_SEPEXTFUNCTORMODTYPEVIAAPPLICATION

#include <utility>

#include "Datatypes.h"
#include "Inner.h"
#include "Nat.h"

namespace SepExtFunctorModtypeViaApplication {

struct NatB {
  using t = Datatypes::Nat;
};

using G = Inner::F<NatB>;

struct YY {
  using u = bool;
  static Datatypes::Nat f(bool b);
};

using H = G::Use<YY>;

template <Inner::F_S<NatB> Z> struct K {
  static typename Datatypes::Nat h(typename Z::u x0_) {
    return Z::f(std::move(x0_));
  }
};

using KK = K<YY>;
template <typename M>
concept S2 = Inner::F_S<M, NatB>;

template <S2 Z> struct K2 {
  static typename Datatypes::Nat h2(typename Z::u x0_) {
    return Z::f(std::move(x0_));
  }
};

using KK2 = K2<YY>;
const bool res =
    Nat::eqb(Nat::add(Nat::add(H::g(true), KK::h(false)), KK2::h2(true)),
             Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::o())));

} // namespace SepExtFunctorModtypeViaApplication

#endif // INCLUDED_SEPEXTFUNCTORMODTYPEVIAAPPLICATION
