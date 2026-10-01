#include <monad_alias_of_applied.h>

#include <cassert>
#include <iostream>

int main() {
  assert(MonadAliasOfApplied::is_three);
  std::cout << "monad_alias_of_applied: ok" << std::endl;
  return 0;
}
