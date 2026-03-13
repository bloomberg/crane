#ifndef INCLUDED_DEPENDENT_TYPENAME
#define INCLUDED_DEPENDENT_TYPENAME

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename M>
concept HasType = requires {
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
concept Container = requires { typename M::t; };

struct DependentTypename {
  template <HasType M> struct UsesType {
    static const typename M::t &get_default() {
      static const typename M::t v = M::default_;
      return v;
    }

    __attribute__((pure)) static typename M::t identity(const typename M::t x) {
      return x;
    }

    static const typename M::t &make_default() {
      static const typename M::t v = M::default_;
      return v;
    }
  };

  struct NatType {
    using t = unsigned int;
    static inline const t default_ = 42u;
  };

  using NatUser = UsesType<NatType>;
  static inline const NatType::t test = NatUser::get_default();

  template <Container C> struct UseContainer {
    static const typename C::template t<unsigned int> &make_nat_container() {
      static const typename C::template t<unsigned int> v =
          C::template empty<unsigned int>;
      return v;
    }

    __attribute__((pure)) static typename C::template t<unsigned int>
    use_singleton(const unsigned int _x0) {
      return C::template singleton<unsigned int>(_x0);
    }
  };
};

#endif // INCLUDED_DEPENDENT_TYPENAME
