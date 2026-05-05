#ifndef INCLUDED_SEPEXTMODULEABBREV
#define INCLUDED_SEPEXTMODULEABBREV

#include <memory>
#include <optional>
#include <type_traits>

namespace SepExtModuleAbbrev {

template <typename M>
concept OrderedType = requires { typename M::t; };
template <typename M>
concept WS = requires {
  requires OrderedType<typename M::E>;
  typename M::key;
};

template <OrderedType X, WS M> struct OrdFacts {
  static bool key_eq(const typename M::key, const typename M::key) {
    return true;
  }

  static bool ord_eq(const typename X::t, const typename X::t) { return true; }
};

template <WS M> struct KeyFacts {
  using ME = typename M::E;
};

template <WS P> struct WFacts : OrdFacts<typename P::E, P> {};

} // namespace SepExtModuleAbbrev

#endif // INCLUDED_SEPEXTMODULEABBREV
