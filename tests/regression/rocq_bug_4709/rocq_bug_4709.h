#ifndef INCLUDED_ROCQ_BUG_4709
#define INCLUDED_ROCQ_BUG_4709

#include <any>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct RocqBug4709 {
  enum class T { e_FOO };
  using foo = std::any;
  using ty = unsigned int;
  static inline const ty check = 42u;
};

#endif // INCLUDED_ROCQ_BUG_4709
