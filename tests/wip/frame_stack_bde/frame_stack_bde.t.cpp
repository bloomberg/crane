#include <frame_stack_bde.h>

#include <iostream>

int main() {
  auto t = FrameStackBde::total;
  bool s = FrameStackBde::all_small;
  std::cout << t << " " << s << std::endl;
  return (t == 6 && s) ? 0 : 1;
}
