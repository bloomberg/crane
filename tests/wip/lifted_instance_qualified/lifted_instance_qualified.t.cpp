#include <lifted_instance_qualified.h>

#include <cassert>

int main() {
  // "o" ++ "u" ++ "n"
  assert(LiftedInstanceQualified::use(Nat::o()).size() == 3);
  return 0;
}
