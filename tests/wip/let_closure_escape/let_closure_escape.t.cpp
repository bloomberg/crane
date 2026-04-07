#include <let_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using LCE = LetClosureEscape;

  // let_escape creates a [&] lambda (sum_values t) bound to variable f,
  // then returns f. return_captures_by_value doesn't convert f to [=]
  // because it only matches Sreturn(Some(CPPlambda)), not Sreturn(Some(CPPvar)).
  // Expected if correct: sum_values(Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf), 0) = 60
  auto r = LCE::bug_let_clobber;
  std::cout << "bug_let_clobber = " << r << std::endl;
  assert(r == 60u);

  std::cout << "All let_closure_escape tests passed!" << std::endl;
  return 0;
}
