#include <partial_app_move.h>

#include <cassert>
#include <iostream>

int main() {
  using PM = PartialAppMove;

  // inline_bug2 crashes at static init time:
  //   t is a local shared_ptr
  //   f = sum_values t  (partial app → [&] lambda capturing t by reference)
  //   w = wrap(std::move(t))  (escape analysis incorrectly moves t!)
  //   f(99) dereferences moved-from t → SEGV
  //
  // Expected: 159 (10+30+20+99)
  // Actual: SEGV (null pointer dereference)
  auto result = PM::inline_bug2;
  std::cout << "inline_bug2 = " << result << std::endl;
  assert(result == 159u);

  std::cout << "All partial_app_move tests passed!" << std::endl;
  return 0;
}
