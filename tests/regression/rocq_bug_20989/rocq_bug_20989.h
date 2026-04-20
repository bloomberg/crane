#ifndef INCLUDED_ROCQ_BUG_20989
#define INCLUDED_ROCQ_BUG_20989

#include <concepts>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <typename M>
concept S = requires {
  requires(
      requires {
        { M::n } -> std::convertible_to<unsigned int>;
      } ||
      requires {
        { M::n() } -> std::convertible_to<unsigned int>;
      });
};

struct RocqBug20989 {
  struct A {
    static inline const unsigned int n = 0u;
  };

  template <S X> struct M {
    using In = X;

    static const unsigned int &n() {
      static const unsigned int v = In::n;
      return v;
    }
  };

  using N = M<A>;
};

#endif // INCLUDED_ROCQ_BUG_20989
