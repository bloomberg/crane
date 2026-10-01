#ifndef INCLUDED_SEPEXTFUNTYPEQUAL
#define INCLUDED_SEPEXTFUNTYPEQUAL

#include "fn.h"
#include <concepts>

namespace SepExtFunTypeQual {

template <typename M>
concept S = requires {
  typename M::elt;
  typename M::t;
  {
    M::for_all(std::declval<crane::fn<bool(typename M::elt)>>(),
               std::declval<typename M::t>())
  } -> std::same_as<bool>;
  {
    M::exists_(std::declval<crane::fn<bool(typename M::elt)>>(),
               std::declval<typename M::t>())
  } -> std::same_as<bool>;
  {
    M::filter(std::declval<crane::fn<bool(typename M::elt)>>(),
              std::declval<typename M::t>())
  } -> std::same_as<typename M::t>;
};

template <S M> struct MyModule {
  static typename M::t test(typename M::t x) { return x; }
};

} // namespace SepExtFunTypeQual

#endif // INCLUDED_SEPEXTFUNTYPEQUAL
