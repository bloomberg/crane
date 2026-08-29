#ifndef INCLUDED_SEPEXTCLONECTORQUAL
#define INCLUDED_SEPEXTCLONECTORQUAL

#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SepExtCloneCtorQual {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <OrderedType X> struct FMapList {
  template <typename T1>
  static bool has_tail(
      const typename Datatypes::template List<std::pair<typename X::t, T1>> &l,
      const T1 &) {
    if (std::holds_alternative<typename Datatypes::template List<
            std::pair<typename X::t, T1>>::Nil>(l.v())) {
      return false;
    } else {
      return true;
    }
  }
};

} // namespace SepExtCloneCtorQual

#endif // INCLUDED_SEPEXTCLONECTORQUAL
