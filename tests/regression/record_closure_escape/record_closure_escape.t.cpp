#include <record_closure_escape.h>

#include <cassert>
#include <iostream>

int main() {
  using RCE = RecordClosureEscape;

  // record_escape stores a [&] closure in a record field.
  // When the function returns, the captured parameter is destroyed.
  // Expected if correct: sum_values(t1, 42) with t1 = Node(Node(Leaf,10,Leaf),20,Node(Leaf,30,Leaf))
  // = lv + rv + v + x = 10 + 30 + 20 + 42 = 102
  auto r = RCE::bug_record_escape;
  std::cout << "bug_record_escape = " << r << std::endl;
  assert(r == 102u);

  std::cout << "All record_closure_escape tests passed!" << std::endl;
  return 0;
}
