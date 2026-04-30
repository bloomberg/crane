#ifndef INCLUDED_NAT_MOD_ZERO
#define INCLUDED_NAT_MOD_ZERO

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NatModZero {
  /// In Rocq, Nat.modulo n 0 = n — perfectly defined.
  /// But NatIntStd maps Nat.modulo to (%a0 % %a1) with
  /// no zero guard — unlike Nat.div which has one.
  /// So my_mod n 0 produces n % 0u in C++ — UB (SIGFPE).
  static unsigned int my_mod(const unsigned int &_x0, const unsigned int &_x1);
  /// A "safe" divmod that a Rocq programmer would reasonably write,
  /// relying on the totality of Nat.div and Nat.modulo.
  /// In Rocq, divmod n 0 = (0, n).
  /// In C++, the second component triggers UB.
  static std::pair<unsigned int, unsigned int> divmod(const unsigned int &a,
                                                      const unsigned int &b);
};

#endif // INCLUDED_NAT_MOD_ZERO
