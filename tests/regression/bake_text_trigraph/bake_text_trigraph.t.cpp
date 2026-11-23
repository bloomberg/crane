#include <bake_text_trigraph.h>

#include <cassert>
#include <iostream>

int main() {
  auto t = BakeTextTrigraph::total;
  std::cout << "total = " << t << std::endl;
  assert(t == 24);
  return 0;
}
