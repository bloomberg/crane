#include "sequential_monad_alias.h"

void SequentialMonadAlias::direct() {
  std::cout << std::string("direct") << '\n';
  return;
}

SequentialMonadAlias::IOt<std::monostate>
SequentialMonadAlias::twice(const std::monostate &m) {
  m;
  return m;
}
