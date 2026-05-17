#ifndef INCLUDED_SEPEXTPROPERASEDUSING
#define INCLUDED_SEPEXTPROPERASEDUSING

namespace SepExtPropErasedUsing {

template <typename M>
concept OrderedType = requires { typename M::t; };

template <OrderedType X> struct FMapList {
  constexpr static bool eq_key(typename X::t, typename X::t) { return true; }
};

} // namespace SepExtPropErasedUsing

#endif // INCLUDED_SEPEXTPROPERASEDUSING
