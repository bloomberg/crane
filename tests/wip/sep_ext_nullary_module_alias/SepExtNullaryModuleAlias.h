#ifndef INCLUDED_SEPEXTNULLARYMODULEALIAS
#define INCLUDED_SEPEXTNULLARYMODULEALIAS

#include <concepts>

namespace SepExtNullaryModuleAlias {

template <typename M>
concept HasVal = requires {
  typename M::t;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::t>;
      });
};
template <typename M>
concept Config = requires {
  requires HasVal<typename M::V>;
  requires(
      requires {
        { M::default_val } -> std::convertible_to<uint64_t>;
      } ||
      requires {
        { M::default_val() } -> std::convertible_to<uint64_t>;
      });
};

template <Config C> struct Worker {
  using MyV = typename C::V;

  static const typename MyV::t &get_empty() {
    static const typename MyV::t v = MyV::empty();
    return v;
  }

  static const uint64_t &get_default() {
    static const uint64_t v = C::default_val();
    return v;
  }
};

} // namespace SepExtNullaryModuleAlias

#endif // INCLUDED_SEPEXTNULLARYMODULEALIAS
