#ifndef INCLUDED_SEPEXTNULLARYDEEPPATH
#define INCLUDED_SEPEXTNULLARYDEEPPATH

#include <concepts>

namespace SepExtNullaryDeepPath {

template <typename M>
concept Leaf = requires {
  requires(
      requires {
        { M::val } -> std::convertible_to<uint64_t>;
      } ||
      requires {
        { M::val() } -> std::convertible_to<uint64_t>;
      });
  requires(
      requires {
        { M::extra } -> std::convertible_to<uint64_t>;
      } ||
      requires {
        { M::extra() } -> std::convertible_to<uint64_t>;
      });
};
template <typename M>
concept Mid = requires { requires Leaf<typename M::L>; };
template <typename M>
concept Root = requires { requires Mid<typename M::M>; };

template <Root R> struct Worker {
  static const uint64_t &deep_val() {
    static const uint64_t v = R::M::L::val();
    return v;
  }

  static const uint64_t &deep_extra() {
    static const uint64_t v = R::M::L::extra();
    return v;
  }

  static const uint64_t &deep_sum() {
    static const uint64_t v = (R::M::L::val() + R::M::L::extra());
    return v;
  }
};

} // namespace SepExtNullaryDeepPath

#endif // INCLUDED_SEPEXTNULLARYDEEPPATH
