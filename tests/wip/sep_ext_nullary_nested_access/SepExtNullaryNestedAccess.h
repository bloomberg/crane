#ifndef INCLUDED_SEPEXTNULLARYNESTEDACCESS
#define INCLUDED_SEPEXTNULLARYNESTEDACCESS

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>

namespace SepExtNullaryNestedAccess {

template <typename M>
concept Inner = requires {
  requires(
      requires {
        { M::val } -> std::convertible_to<unsigned int>;
      } ||
      requires {
        { M::val() } -> std::convertible_to<unsigned int>;
      });
};
template <typename M>
concept Outer = requires {
  requires Inner<typename M::I>;
  requires(
      requires {
        { M::name } -> std::convertible_to<unsigned int>;
      } ||
      requires {
        { M::name() } -> std::convertible_to<unsigned int>;
      });
};

template <Outer O> struct Worker {
  static const unsigned int &get_inner_val() {
    static const unsigned int v = O::I::val();
    return v;
  }

  static const unsigned int &get_name() {
    static const unsigned int v = O::name();
    return v;
  }

  static const unsigned int &sum() {
    static const unsigned int v = (O::I::val() + O::name());
    return v;
  }
};

} // namespace SepExtNullaryNestedAccess

#endif // INCLUDED_SEPEXTNULLARYNESTEDACCESS
