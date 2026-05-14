#ifndef INCLUDED_SEPEXTPROPERASEDUSING
#define INCLUDED_SEPEXTPROPERASEDUSING

#include <memory>
#include <optional>
#include <type_traits>

namespace SepExtPropErasedUsing {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <OrderedType X> struct FMapList {
  constexpr static bool eq_key(const typename X::t, const typename X::t) {
    return true;
  }
};

} // namespace SepExtPropErasedUsing

#endif // INCLUDED_SEPEXTPROPERASEDUSING
