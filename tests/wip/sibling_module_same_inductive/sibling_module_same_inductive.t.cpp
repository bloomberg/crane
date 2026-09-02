#include <sibling_module_same_inductive.h>
#include <cassert>

int main() {
  assert(std::holds_alternative<typename Nat::S>(
      SiblingModuleSameInductive::run(Nat::s(Nat::o())).v()));
  assert(SiblingModuleSameInductive::run2(Bool0::TRUE_) == Bool0::TRUE_);
  return 0;
}
