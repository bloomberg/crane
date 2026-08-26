#include <sig_curried_payload.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = SigCurriedPayload::go;
  std::cout << "go = " << r << " (want 3)" << std::endl;
  assert(r == 3);
  return 0;
}
