#ifndef INCLUDED_ACK
#define INCLUDED_ACK

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Nat {
  static inline const unsigned int one = 1u;
};

struct Ack {
  static unsigned int ack(unsigned int m, const unsigned int &n);
};

#endif // INCLUDED_ACK
