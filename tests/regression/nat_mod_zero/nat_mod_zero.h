#ifndef INCLUDED_NAT_MOD_ZERO
#define INCLUDED_NAT_MOD_ZERO

#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct NatModZero {
  /// In Rocq, Nat.modulo n 0 = n — perfectly defined.
  /// But NatIntStd maps Nat.modulo to (%a0 % %a1) with
  /// no zero guard — unlike Nat.div which has one.
  /// So my_mod n 0 produces n % 0u in C++ — UB (SIGFPE).
  __attribute__((pure)) static unsigned int my_mod(const unsigned int _x0,
                                                   const unsigned int _x1);
  /// A "safe" divmod that a Rocq programmer would reasonably write,
  /// relying on the totality of Nat.div and Nat.modulo.
  /// In Rocq, divmod n 0 = (0, n).
  /// In C++, the second component triggers UB.
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int a, const unsigned int b);
};

#endif // INCLUDED_NAT_MOD_ZERO
