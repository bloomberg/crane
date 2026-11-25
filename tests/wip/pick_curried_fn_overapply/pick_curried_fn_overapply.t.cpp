#include <pick_curried_fn_overapply.h>
#include <iostream>
int main() {
  std::cout << PickCurriedFnOverapply::result << std::endl;
  return PickCurriedFnOverapply::result == 30 ? 0 : 1;
}
