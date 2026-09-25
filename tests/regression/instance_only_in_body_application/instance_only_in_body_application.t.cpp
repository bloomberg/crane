#include <cassert>
#include <instance_only_in_body_application.h>

int main() {
  assert(std::holds_alternative<Nat::O>(
      InstanceOnlyInBodyApplication::run.v()));
  return 0;
}
