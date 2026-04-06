#include <deep_destruct.h>

#include <cassert>
#include <iostream>

int main() {
  // Build a linked list of 10,000 elements.
  // Construction is iterative (loopified), so it does not overflow.
  // Destruction, however, triggers a chain of ~10,000 nested shared_ptr
  // destructor calls — one per cons cell — which overflows the C++ stack.
  // (The exact threshold on macOS is ~7,500–8,000 elements.)
  unsigned int result;
  {
    auto l = DeepDestruct::build(10000u);
    result = DeepDestruct::head_or_zero(l);
    std::cout << "Built list, head = " << result << std::endl;
    // l goes out of scope here → deep destructor chain → stack overflow
  }
  std::cout << "List dropped successfully" << std::endl;
  assert(result == 1u);
  return 0;
}
