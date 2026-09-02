#include <submodule_named_nat.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename ::Nat::S>(
      SubmoduleNamedNat::run(::Nat::o()).v()));
  return 0;
}
