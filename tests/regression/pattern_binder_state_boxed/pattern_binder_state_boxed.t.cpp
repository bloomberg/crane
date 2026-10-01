#include <pattern_binder_state_boxed.h>

#include <iostream>

int main() {
  auto t = PatternBinderStateBoxed::t;
  (void)t;
  std::cout << "pattern_binder_state_boxed: ok" << std::endl;
  return 0;
}
