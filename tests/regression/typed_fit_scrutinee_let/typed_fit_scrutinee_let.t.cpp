#include <typed_fit_scrutinee_let.h>

#include <cassert>
#include <iostream>

int main() {
  using T = TypedFitScrutineeLet;
  assert(T::on_t3(true, 4) == 0);
  assert(T::on_t3(false, 4) == 1);
  assert(T::on_z(true, 4) == 0);
  assert(T::on_z(false, 4) == 1);
  std::cout << "ok" << std::endl;
  return 0;
}
