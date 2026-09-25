#include <cassert>
#include <two_instances_disagree_on_promoted_name.h>

int main() {
  assert(std::holds_alternative<Nat::O>(
      TwoInstancesDisagreeOnPromotedName::run.v()));
  return 0;
}
