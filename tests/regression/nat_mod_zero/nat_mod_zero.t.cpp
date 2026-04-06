#include <nat_mod_zero.h>

#include <cassert>
#include <iostream>

int main() {
  // In Rocq: Nat.modulo 42 0 = 42 (total function, well-defined)
  // In C++:  42u % 0u  is undefined behavior (typically SIGFPE)
  //
  // NatIntStd maps Nat.div with a zero guard:
  //   (%a1 ? %a0 / %a1 : 0)
  // but Nat.modulo WITHOUT one:
  //   (%a0 % %a1)

  // This crashes (SIGFPE):
  auto result = NatModZero::my_mod(42u, 0u);
  std::cout << "my_mod(42, 0) = " << result << std::endl;
  assert(result == 42u);

  // divmod also crashes due to the modulo component:
  auto [q, r] = NatModZero::divmod(42u, 0u);
  std::cout << "divmod(42, 0) = (" << q << ", " << r << ")" << std::endl;
  assert(q == 0u);
  assert(r == 42u);

  return 0;
}
