#ifndef INCLUDED_INNER
#define INCLUDED_INNER

#include <concepts>
#include <utility>

namespace Inner {

template <typename M, typename X>
concept F_S = requires {
  typename M::u;
  { M::f(std::declval<typename M::u>()) } -> std::same_as<typename X::t>;
};
template <typename M>
concept Base = requires { typename M::t; };

template <Base X> struct F {
  template <F_S<X> Y> struct Use {
    static typename X::t g(typename Y::u x0_) { return Y::f(std::move(x0_)); }
  };
};

} // namespace Inner

#endif // INCLUDED_INNER
