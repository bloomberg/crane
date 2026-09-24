#include "error_ctor_through_monad_instance.h"
#include <cassert>

int main() {
  assert(
      std::holds_alternative<Nat::S>(ErrorCtorThroughMonadInstance::run.v()));
  return 0;
}
