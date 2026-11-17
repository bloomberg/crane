#pragma once

namespace SepExtPropErasedUsing {
template <typename M>
concept OrderedType = requires {
  typename M::t;
};

template <OrderedType X> struct FMapList {
  static bool eq_key(typename X::t, typename X::t) { return true; }
};
} // namespace SepExtPropErasedUsing
