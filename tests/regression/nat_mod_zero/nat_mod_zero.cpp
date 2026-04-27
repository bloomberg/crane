#include <nat_mod_zero.h>

/// In Rocq, Nat.modulo n 0 = n — perfectly defined.
/// But NatIntStd maps Nat.modulo to (%a0 % %a1) with
/// no zero guard — unlike Nat.div which has one.
/// So my_mod n 0 produces n % 0u in C++ — UB (SIGFPE).
__attribute__((pure)) unsigned int NatModZero::my_mod(const unsigned int &_x0,
                                                      const unsigned int &_x1) {
  return (_x1 ? _x0 % _x1 : _x0);
}

/// A "safe" divmod that a Rocq programmer would reasonably write,
/// relying on the totality of Nat.div and Nat.modulo.
/// In Rocq, divmod n 0 = (0, n).
/// In C++, the second component triggers UB.
__attribute__((pure)) std::pair<unsigned int, unsigned int>
NatModZero::divmod(const unsigned int &a, const unsigned int &b) {
  return std::make_pair((b ? a / b : 0), (b ? a % b : a));
}
