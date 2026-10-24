#include "sequential_monad_alias.h"

void SequentialMonadAlias::aliased() {
  std::cout << std::string("aliased") << '\n';
  return;
}

void SequentialMonadAlias::direct() {
  std::cout << std::string("direct") << '\n';
  return;
}

void SequentialMonadAlias::both() {
  aliased();
  {
    direct();
    return;
  }
}

void SequentialMonadAlias::twice(const std::monostate &m) {
  m;
  return;
}
