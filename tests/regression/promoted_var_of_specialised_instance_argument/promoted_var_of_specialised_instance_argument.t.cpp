#include <cassert>
#include <promoted_var_of_specialised_instance_argument.h>

int main() {
  assert(std::holds_alternative<Nat::S>(
      PromotedVarOfSpecialisedInstanceArgument::run.v()));
  return 0;
}
