#include <closure_capture_match.h>

#include <cassert>
#include <iostream>

int main() {
  using CM = ClosureCaptureMatch;

  // Test test_capture: this is computed at static init time.
  // The generated code has a use-after-move bug:
  //   t is captured by reference in closure f,
  //   then t is moved away into box_from_match,
  //   then f(5u) accesses the moved-from t.
  // In Rocq, deep_capture t produces a closure that has t's data
  // baked in (partial application). In C++, the "partial application"
  // is a lambda capturing t by reference, which goes stale after the move.
  auto result = CM::test_capture;
  std::cout << "test_capture = " << result << std::endl;
  // deep_capture on Node(Node(Leaf,10,Leaf), 20, Node(Leaf,30,Leaf)):
  //   lv=10, rv=30, v=20, f(5) = 10+30+20+5 = 65
  // box_from_match: Box(fun x => 20 + x), unbox(b, 7) = 27
  // Total: 65 + 27 = 92
  assert(result == 92u);

  std::cout << "All closure capture tests passed!" << std::endl;
  return 0;
}
