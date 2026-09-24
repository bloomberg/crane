#include <cassert>
#include <instance_method_param_at_class_carrier.h>

int main() {
  using NS = InstanceMethodParamAtClassCarrier;
  assert(std::holds_alternative<Nat::S>(NS::run.v()));
  return 0;
}
