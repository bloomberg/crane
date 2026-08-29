#ifndef INCLUDED_SEPEXTTHISINFREEFN
#define INCLUDED_SEPEXTTHISINFREEFN

#include "Datatypes.h"
#include "ListDef.h"

namespace SepExtThisInFreeFn {

template <typename M>
concept S = requires { typename M::t; };

template <S X> struct FreeFn {
  template <typename T1>
  static typename Datatypes::template List<typename Datatypes::Nat>
  map_lengths(const typename Datatypes::template List<
              typename Datatypes::template List<T1>> &xss) {
    return xss.template map<typename Datatypes::Nat>(
        [](const auto &_x) { return _x.length(); });
  }
};

} // namespace SepExtThisInFreeFn

#endif // INCLUDED_SEPEXTTHISINFREEFN
