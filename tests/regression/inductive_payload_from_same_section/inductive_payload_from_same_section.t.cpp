#include <cassert>
#include <inductive_payload_from_same_section.h>

int main() {
  assert(std::holds_alternative<Nat::O>(
      InductivePayloadFromSameSection::run.v()));
  return 0;
}
