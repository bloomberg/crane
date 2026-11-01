#ifndef INCLUDED_SEPEXTFUNCTORINCLUDE
#define INCLUDED_SEPEXTFUNCTORINCLUDE

#include <utility>

#include "Datatypes.h"
#include "Nat.h"
#include "Ord.h"

namespace SepExtFunctorInclude {

template <Ord::Ordered O> struct Tac {
  using F = Ord::template Full<O>;

  static bool gtb(typename O::t x, typename O::t y) {
    return !(F::geb(std::move(y), std::move(x)));
  }
};

struct NatOrd {
  using t = Datatypes::Nat;
  static bool leb(const Datatypes::Nat &x0_, const Datatypes::Nat &x1_);
};

using T = Tac<NatOrd>;
const bool gt_two_one =
    T::gtb(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::o())),
           Datatypes::Nat::s(Datatypes::Nat::o()));

} // namespace SepExtFunctorInclude

#endif // INCLUDED_SEPEXTFUNCTORINCLUDE
