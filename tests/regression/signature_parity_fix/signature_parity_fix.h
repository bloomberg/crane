#ifndef INCLUDED_SIGNATURE_PARITY_FIX
#define INCLUDED_SIGNATURE_PARITY_FIX

#include <functional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct SignatureParityFix {
  __attribute__((pure)) static unsigned int f(const unsigned int seed);
  static inline const unsigned int t = f(4u);
};

#endif // INCLUDED_SIGNATURE_PARITY_FIX
