#ifndef INCLUDED_DEPENDENT_TYPENAME
#define INCLUDED_DEPENDENT_TYPENAME

#include <concepts>

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
concept Container = requires { typename M::template t<void>; };

struct DependentTypename {
  template <HasType M> struct UsesType {
    static const typename M::t &get_default() {
      static const typename M::t v = M::default_;
      return v;
    }

    static typename M::t identity(typename M::t x) { return x; }

    static const typename M::t &make_default() {
      static const typename M::t v = M::default_;
      return v;
    }
  };

  struct NatType {
    using t = uint64_t;
    static inline const t default_ = UINT64_C(42);
  };

  using NatUser = UsesType<NatType>;
  static inline const NatType::t test = NatUser::get_default();

  template <Container C> struct UseContainer {
    static const typename C::template t<uint64_t> &make_nat_container() {
      static const typename C::template t<uint64_t> v =
          C::template empty<uint64_t>;
      return v;
    }

    static typename C::template t<uint64_t> use_singleton(uint64_t _x0) {
      return C::template singleton<uint64_t>(_x0);
    }
  };
};

#endif // INCLUDED_DEPENDENT_TYPENAME
