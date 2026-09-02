#include <cassert>
#include <sibling_module_same_inductive.h>

int main() {
  assert(std::holds_alternative<typename Nat::S>(
      SiblingModuleSameInductive::run(Nat::s(Nat::o())).v()));
  assert(SiblingModuleSameInductive::run2(true));
  return 0;
}
