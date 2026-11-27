#include "sequential_monad_alias.h"

void SequentialMonadAlias::aliased() {
  std::cout << std::string("aliased") << '\n';
}

void SequentialMonadAlias::direct() {
  std::cout << std::string("direct") << '\n';
}

void SequentialMonadAlias::both() {
  aliased();
  {
    direct();
  }
}

void SequentialMonadAlias::twice(const std::monostate &m) { m; }
