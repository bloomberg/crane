#ifndef INCLUDED_ORD
#define INCLUDED_ORD

#include <concepts>
#include <utility>

namespace Ord {

template <typename M>
concept Ordered = requires {
  typename M::t;
  {
    M::leb(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<bool>;
};

template <Ordered O> struct Full {
  using t = typename O::t;

  static bool geb(typename O::t x, typename O::t y) {
    return O::leb(std::move(y), std::move(x));
  }
};

} // namespace Ord

#endif // INCLUDED_ORD
