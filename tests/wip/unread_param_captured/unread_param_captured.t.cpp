#include <unread_param_captured.h>

#include <iostream>

int main() {
  auto a = UnreadParamCaptured::result;
  std::cout << a << std::endl;
  return a == 3 ? 0 : 1;
}
