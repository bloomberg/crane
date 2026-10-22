#include "sequential_monad_alias.h"

int main() {
  using M = SequentialMonadAlias;
  M::both();
  return 0;
}
