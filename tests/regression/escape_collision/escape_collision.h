#ifndef INCLUDED_ESCAPE_COLLISION
#define INCLUDED_ESCAPE_COLLISION

#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct EscapeCollision {
  __attribute__((pure)) static unsigned int double_(unsigned int n);
  __attribute__((pure)) static unsigned int double_0(unsigned int n);
  static inline const unsigned int t = (double_(1u) + double_0(2u));
};

#endif // INCLUDED_ESCAPE_COLLISION
