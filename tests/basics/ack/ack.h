#ifndef INCLUDED_ACK
#define INCLUDED_ACK

#include <functional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  static inline const unsigned int one = 1u;
};

struct Ack {
  __attribute__((pure)) static unsigned int ack(const unsigned int m,
                                                const unsigned int n);
};

#endif // INCLUDED_ACK
