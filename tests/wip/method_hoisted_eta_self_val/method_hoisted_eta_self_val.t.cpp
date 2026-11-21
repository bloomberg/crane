#include <method_hoisted_eta_self_val.h>

#include <iostream>

int main() {
  auto a = MethodHoistedEtaSelfVal::t_1;
  std::cout << a << std::endl;
  return a == 4 ? 0 : 1;
}
