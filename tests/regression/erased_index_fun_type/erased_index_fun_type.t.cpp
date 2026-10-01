// Crane bug: an erased value in call position.
//
// [ty] is indexed by a Type that can be a function type, so [dflt] is declared
// as returning [crane::obj].  The call site then applies the result directly:
//   error: type 'crane::obj' does not provide a call operator

#include <erased_index_fun_type.h>

#include <cassert>

int main() {
  int k = 0;
  const Nat *p = &ErasedIndexFunType::run;
  while (const auto *s = std::get_if<Nat::S>(&p->v())) {
    ++k;
    p = s->a0.get();
  }
  assert(k == 0); // dflt (TF ...) is [fun _ => dflt TN], i.e. [fun _ => 0]
  return 0;
}
