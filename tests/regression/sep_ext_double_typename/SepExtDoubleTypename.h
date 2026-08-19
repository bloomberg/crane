#ifndef INCLUDED_SEPEXTDOUBLETYPENAME
#define INCLUDED_SEPEXTDOUBLETYPENAME

#include <memory>
#include <optional>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SepExtDoubleTypename {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <OrderedType X> struct FMapList {
  template <typename T1>
  static bool
  is_empty(const typename Datatypes::template List<std::pair<typename X::t, T1>>
               &l) {
    if (std::holds_alternative<typename Datatypes::template List<
            std::pair<typename X::t, T1>>::Nil>(l.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1>
  static std::optional<typename X::t>
  head_key(const typename Datatypes::template List<std::pair<typename X::t, T1>>
               &l) {
    if (std::holds_alternative<typename Datatypes::template List<
            std::pair<typename X::t, T1>>::Nil>(l.v())) {
      return std::optional<typename X::t>();
    } else {
      const auto &[a0, a1] = std::get<typename Datatypes::template List<
          std::pair<typename X::t, T1>>::Cons>(l.v());
      const auto &[k, _x0] = a0;
      return std::make_optional<typename X::t>(k);
    }
  }
};

} // namespace SepExtDoubleTypename

#endif // INCLUDED_SEPEXTDOUBLETYPENAME
