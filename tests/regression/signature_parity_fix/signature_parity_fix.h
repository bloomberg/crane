#ifndef INCLUDED_SIGNATURE_PARITY_FIX
#define INCLUDED_SIGNATURE_PARITY_FIX

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SignatureParityFix {
  __attribute__((pure)) static unsigned int f(unsigned int seed);
  static inline const unsigned int t = f(4u);
};

#endif // INCLUDED_SIGNATURE_PARITY_FIX
