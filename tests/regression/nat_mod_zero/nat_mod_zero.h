#ifndef INCLUDED_NAT_MOD_ZERO
#define INCLUDED_NAT_MOD_ZERO

#include <utility>

struct NatModZero {
  /// In Rocq, Nat.modulo n 0 = n — perfectly defined.
  /// But NatIntStd maps Nat.modulo to (%a0 % %a1) with
  /// no zero guard — unlike Nat.div which has one.
  /// So my_mod n 0 produces n % 0u in C++ — UB (SIGFPE).
  static uint64_t my_mod(uint64_t x0_, uint64_t x1_);
  /// A "safe" divmod that a Rocq programmer would reasonably write,
  /// relying on the totality of Nat.div and Nat.modulo.
  /// In Rocq, divmod n 0 = (0, n).
  /// In C++, the second component triggers UB.
  static std::pair<uint64_t, uint64_t> divmod(uint64_t a, uint64_t b);
};

#endif // INCLUDED_NAT_MOD_ZERO
