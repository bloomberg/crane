#include <type_valued_if_eliminator.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::O>(TypeValuedIfEliminator::run.v()));
  return 0;
}
