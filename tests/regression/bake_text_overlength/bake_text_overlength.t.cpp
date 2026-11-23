#include <bake_text_overlength.h>

#include <cassert>
#include <iostream>

int main() {
  auto t = BakeTextOverlength::total;
  std::cout << "total = " << t << std::endl;
  assert(t == 70000);
  return 0;
}
