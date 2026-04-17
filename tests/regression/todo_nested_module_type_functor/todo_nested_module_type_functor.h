#ifndef INCLUDED_TODO_NESTED_MODULE_TYPE_FUNCTOR
#define INCLUDED_TODO_NESTED_MODULE_TYPE_FUNCTOR

#include <concepts>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename M>
concept INNER = requires {
  typename M::t;
  requires(
      requires {
        { M::zero } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::zero() } -> std::convertible_to<typename M::t>;
      });
};

template <typename M>
concept OUTER = requires { requires INNER<typename M::X>; };

struct TodoNestedModuleTypeFunctor {
  template <OUTER Y> struct Use {
    using Lifted = Y::template Make<Y::X>;

    static const typename Lifted::t &test_value() {
      static const typename Lifted::t v = Lifted::zero;
      return v;
    }
  };
};

#endif // INCLUDED_TODO_NESTED_MODULE_TYPE_FUNCTOR
