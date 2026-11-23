#include <frame_plan_rebind.h>

#include <iostream>

int main() {
  bool a = FramePlanRebind::result;
  std::cout << a << std::endl;
  return a ? 0 : 1;
}
