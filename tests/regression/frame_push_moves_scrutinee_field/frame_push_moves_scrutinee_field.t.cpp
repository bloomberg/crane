#include <frame_push_moves_scrutinee_field.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = FramePushMovesScrutineeField::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 21);
  return 0;
}
