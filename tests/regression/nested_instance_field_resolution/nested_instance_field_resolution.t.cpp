#include <cassert>
#include <nested_instance_field_resolution.h>

int main() {
  assert(std::holds_alternative<Nat::O>(NestedInstanceFieldResolution::run.v()));
  return 0;
}
