#include <sigt_type_witness_container.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::S>(SigtTypeWitnessContainer::run.v()));
  return 0;
}
