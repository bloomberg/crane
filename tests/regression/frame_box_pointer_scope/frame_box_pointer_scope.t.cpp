#include <frame_box_pointer_scope.h>

#include <iostream>

int main() {
  auto a = FrameBoxPointerScope::result;
  std::cout << a << std::endl;
  return a == 6 ? 0 : 1;
}
