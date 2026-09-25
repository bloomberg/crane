#include <cassert>
#include <erased_dval_in_container.h>

int main() {
  assert(std::holds_alternative<Nat::O>(ErasedDvalInContainer::run.v()));
  return 0;
}
