#include <match_ctor_closure.h>

#include <cassert>
#include <iostream>

int main() {
  using MCC = MatchCtorClosure;

  // match_and_box on Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf))
  // returns Box(sum_values l) where l = Node(Leaf,10,Leaf)
  // apply_box (Box(sum_values l)) 5 = sum_values(Node(Leaf,10,Leaf), 5) = 10+5 = 15
  auto r = MCC::bug_match_ctor;
  std::cout << "bug_match_ctor = " << r << std::endl;
  assert(r == 15u);

  std::cout << "All match_ctor_closure tests passed!" << std::endl;
  return 0;
}
