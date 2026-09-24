#include <cassert>
#include <instance_method_param_at_foreign_class_field.h>

int main() {
  using NS = InstanceMethodParamAtForeignClassField;
  using Ptr = std::pair<Nat, bool>;
  assert(std::holds_alternative<EOU<Ptr>::Ok>(NS::run.v()));
  return 0;
}
