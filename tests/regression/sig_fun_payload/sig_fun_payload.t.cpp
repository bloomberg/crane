#include <sig_fun_payload.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = SigFunPayload::go;
  std::cout << "go = " << r << " (want 5)" << std::endl;
  assert(r == 5);
  return 0;
}
