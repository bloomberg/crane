#include <let_bound_monad_family.h>

#include <cassert>
#include <iostream>

int main() {
  // Get answered with 2 by h, then S 2 = 3.
  assert(LetBoundMonadFamily::is_three);
  std::cout << "let_bound_monad_family: ok" << std::endl;
  return 0;
}
