#ifndef INCLUDED_ROCQ_BUG_14100
#define INCLUDED_ROCQ_BUG_14100

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename M>
concept MinSIG = requires { typename M::template otherE<void>; };

struct RocqBug14100 {
  enum class NondetE { e_OR };

  struct Min {
    template <typename x> using otherE = NondetE;
  };

  static_assert(MinSIG<Min>);
};

#endif // INCLUDED_ROCQ_BUG_14100
