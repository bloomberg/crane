#include <fold_closure_accum.h>

#include <cassert>
#include <iostream>

int main() {
  using FCA = FoldClosureAccum;

  // fold_bug: compose_adders from 3 trees, apply to 0
  // BUG: compose_adders throws "untranslatable curried proof term"
  // Expected: 10 + 20 + 30 + 0 = 60
  auto r1 = FCA::fold_bug;
  std::cout << "fold_bug = " << r1 << std::endl;
  assert(r1 == 60u);

  // fold_bug_offset: same but starting from 7
  // Expected: 10 + 20 + 30 + 7 = 67
  auto r2 = FCA::fold_bug_offset;
  std::cout << "fold_bug_offset = " << r2 << std::endl;
  assert(r2 == 67u);

  // fold_bug_double: composed function called twice
  // f = compose_adders [t1; t2] = fun x => x + 30
  // f(0) + f(100) = 30 + 130 = 160
  auto r3 = FCA::fold_bug_double;
  std::cout << "fold_bug_double = " << r3 << std::endl;
  assert(r3 == 160u);

  std::cout << "All fold_closure_accum tests passed!" << std::endl;
  return 0;
}
