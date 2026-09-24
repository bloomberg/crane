#include <cassert>
#include <error_ctor_through_reified_instance.h>

int main() {
  using NS = ErrorCtorThroughReifiedInstance;
  assert(std::holds_alternative<Nat::S>(NS::run.v()));
  return 0;
}
