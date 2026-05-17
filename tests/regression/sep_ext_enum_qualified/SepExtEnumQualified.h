#ifndef INCLUDED_SEPEXTENUMQUALIFIED
#define INCLUDED_SEPEXTENUMQUALIFIED

#include <concepts>
#include <utility>

#include "Datatypes.h"

namespace SepExtEnumQualified {

template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Datatypes::Comparison>;
};

template <OrderedType X> struct Make {
  constexpr static bool is_lt(typename X::t a, typename X::t b) {
    switch (X::compare(a, b)) {
    case Datatypes::Comparison::e_LT: {
      return true;
    }
    default: {
      return false;
    }
    }
  }

  constexpr static bool is_eq(typename X::t a, typename X::t b) {
    switch (X::compare(a, b)) {
    case Datatypes::Comparison::e_EQ: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
};

} // namespace SepExtEnumQualified

#endif // INCLUDED_SEPEXTENUMQUALIFIED
