#include <hkt_single_ctor_instance_body.h>
#include <cassert>

int main() {
  auto b = HktSingleCtorInstanceBody::run(Nat::s(Nat::o()));
  (void)b;
  return 0;
}
