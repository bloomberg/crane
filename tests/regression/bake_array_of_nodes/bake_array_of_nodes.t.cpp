#include <bake_array_of_nodes.h>

#include <cassert>
#include <iostream>

int main() {
  auto t = BakeArrayOfNodes::total;
  std::cout << "total = " << t << std::endl;
  assert(t == 21);
  return 0;
}
