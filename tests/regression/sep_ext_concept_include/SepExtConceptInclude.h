#ifndef INCLUDED_SEPEXTCONCEPTINCLUDE
#define INCLUDED_SEPEXTCONCEPTINCLUDE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

namespace SepExtConceptInclude {

template <typename M>
concept BaseType = requires {
  typename M::t;
  requires(
      requires {
        { M::default_ } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::default_() } -> std::convertible_to<typename M::t>;
      });
};
template <typename M>
concept DerivedType = BaseType<M>;

template <DerivedType X> struct Use {
  static const typename X::t &get_default() {
    static const typename X::t v = X::default_();
    return v;
  }
};

} // namespace SepExtConceptInclude

#endif // INCLUDED_SEPEXTCONCEPTINCLUDE
