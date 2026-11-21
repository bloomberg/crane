#include <deque_nil_erased.h>

#include <iostream>

int main() {
  auto a = DequeNilErased::t_1;
  std::cout << a << std::endl;
  return a == 0 ? 0 : 1;
}
