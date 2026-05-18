#include "nat_mod_zero.h"

/// In Rocq, Nat.modulo n 0 = n — perfectly defined.
/// But NatIntStd maps Nat.modulo to (%a0 % %a1) with
/// no zero guard — unlike Nat.div which has one.
/// So my_mod n 0 produces n % 0u in C++ — UB (SIGFPE).
uint64_t NatModZero::my_mod(uint64_t _x0, uint64_t _x1) {
  return (_x1 ? _x0 % _x1 : _x0);
}

/// A "safe" divmod that a Rocq programmer would reasonably write,
/// relying on the totality of Nat.div and Nat.modulo.
/// In Rocq, divmod n 0 = (0, n).
/// In C++, the second component triggers UB.
std::pair<uint64_t, uint64_t> NatModZero::divmod(uint64_t a, uint64_t b) {
  return std::make_pair((b ? a / b : 0), (b ? a % b : a));
}
