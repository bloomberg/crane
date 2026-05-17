#ifndef INCLUDED_SEPEXTNULLARYDEEPPATH
#define INCLUDED_SEPEXTNULLARYDEEPPATH

#include <concepts>

namespace SepExtNullaryDeepPath {

template <typename M>
concept Leaf = requires {
  requires(
      requires {
        { M::val } -> std::convertible_to<unsigned int>;
      } ||
      requires {
        { M::val() } -> std::convertible_to<unsigned int>;
      });
  requires(
      requires {
        { M::extra } -> std::convertible_to<unsigned int>;
      } ||
      requires {
        { M::extra() } -> std::convertible_to<unsigned int>;
      });
};
template <typename M>
concept Mid = requires { requires Leaf<typename M::L>; };
template <typename M>
concept Root = requires { requires Mid<typename M::M>; };

template <Root R> struct Worker {
  static const unsigned int &deep_val() {
    static const unsigned int v = R::M::L::val();
    return v;
  }

  static const unsigned int &deep_extra() {
    static const unsigned int v = R::M::L::extra();
    return v;
  }

  static const unsigned int &deep_sum() {
    static const unsigned int v = (R::M::L::val() + R::M::L::extra());
    return v;
  }
};

} // namespace SepExtNullaryDeepPath

#endif // INCLUDED_SEPEXTNULLARYDEEPPATH
