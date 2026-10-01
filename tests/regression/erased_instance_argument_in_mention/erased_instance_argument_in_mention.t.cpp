#include <cassert>
#include <erased_instance_argument_in_mention.h>

int main() {
  assert(std::holds_alternative<Nat::O>(ErasedInstanceArgumentInMention::run.v()));
  return 0;
}
