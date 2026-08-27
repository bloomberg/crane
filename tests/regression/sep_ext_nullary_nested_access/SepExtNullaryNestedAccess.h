#ifndef INCLUDED_SEPEXTNULLARYNESTEDACCESS
#define INCLUDED_SEPEXTNULLARYNESTEDACCESS

#include <concepts>

namespace SepExtNullaryNestedAccess {

template <typename M>
concept Inner = requires {
  requires(
      requires {
        { M::val } -> std::convertible_to<uint64_t>;
      } ||
      requires {
        { M::val() } -> std::convertible_to<uint64_t>;
      });
};
template <typename M>
concept Outer = requires {
  requires Inner<typename M::I>;
  requires(
      requires {
        { M::name } -> std::convertible_to<uint64_t>;
      } ||
      requires {
        { M::name() } -> std::convertible_to<uint64_t>;
      });
};

template <Outer O> struct Worker {
  static const uint64_t &get_inner_val() {
    static const uint64_t v = [] {
      if constexpr (requires { O::I::val(); })
        return O::I::val();
      else
        return O::I::val;
    }();
    return v;
  }

  static const uint64_t &get_name() {
    static const uint64_t v = [] {
      if constexpr (requires { O::name(); })
        return O::name();
      else
        return O::name;
    }();
    return v;
  }

  static const uint64_t &sum() {
    static const uint64_t v = ([] {
      if constexpr (requires { O::I::val(); })
        return O::I::val();
      else
        return O::I::val;
    }() +
                               [] {
                                 if constexpr (requires { O::name(); })
                                   return O::name();
                                 else
                                   return O::name;
                               }());
    return v;
  }
};

} // namespace SepExtNullaryNestedAccess

#endif // INCLUDED_SEPEXTNULLARYNESTEDACCESS
