#include <iter_capture.h>
#include <cassert>
#include <iostream>

int main() {
  // Rocq: let _acc := 100 in Nat.iter 3 (fun x => x + _acc) 0 = 300.
  std::cout << IterCapture::run << std::endl;
  assert(IterCapture::run == 300);
  return 0;
}
