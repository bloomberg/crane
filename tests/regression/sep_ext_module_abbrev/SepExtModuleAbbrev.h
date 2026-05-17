#ifndef INCLUDED_SEPEXTMODULEABBREV
#define INCLUDED_SEPEXTMODULEABBREV

namespace SepExtModuleAbbrev {

template <typename M>
concept OrderedType = requires { typename M::t; };
template <typename M>
concept WS = requires {
  requires OrderedType<typename M::E>;
  typename M::key;
};

template <OrderedType X, WS M> struct OrdFacts {
  constexpr static bool key_eq(typename M::key, typename M::key) {
    return true;
  }

  constexpr static bool ord_eq(typename X::t, typename X::t) { return true; }
};

template <WS M> struct KeyFacts {
  using ME = typename M::E;
};

template <WS P> struct WFacts : OrdFacts<typename P::E, P> {};

} // namespace SepExtModuleAbbrev

#endif // INCLUDED_SEPEXTMODULEABBREV
