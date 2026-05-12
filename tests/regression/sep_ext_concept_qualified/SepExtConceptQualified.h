#ifndef INCLUDED_SEPEXTCONCEPTQUALIFIED
#define INCLUDED_SEPEXTCONCEPTQUALIFIED

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

#include "Datatypes.h"

namespace SepExtConceptQualified {

template <typename M>
concept OrderedType = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Datatypes::Comparison>;
};

template <OrderedType X> struct Make {
  constexpr static bool is_eq(const typename X::t a, const typename X::t b) {
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

} // namespace SepExtConceptQualified

#endif // INCLUDED_SEPEXTCONCEPTQUALIFIED
