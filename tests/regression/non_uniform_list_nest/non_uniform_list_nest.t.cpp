#include <non_uniform_list_nest.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = NonUniformListNest::go;
  std::cout << "go = " << r << " (want 1)" << std::endl;
  assert(r == 1);
  return 0;
}
