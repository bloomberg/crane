#include <cassert>
#include <instance_carrier_unqualified_at_known_instance.h>

int main() {
  using Ptr = std::pair<Nat, bool>;
  assert(std::holds_alternative<EOU<Ptr>::Ok>(
      InstanceCarrierUnqualifiedAtKnownInstance::run.v()));
  return 0;
}
