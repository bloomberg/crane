#include "error_ctor_type_from_enclosing_return.h"
#include <cassert>

int main() {
  assert(std::holds_alternative<Nat::S>(
      ErrorCtorTypeFromEnclosingReturn::run.v()));
  return 0;
}
