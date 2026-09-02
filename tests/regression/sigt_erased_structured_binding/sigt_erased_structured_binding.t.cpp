#include <sigt_erased_structured_binding.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::S>(SigtErasedStructuredBinding::run.v()));
  return 0;
}
