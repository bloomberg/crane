#include <inductive_named_list.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = InductiveNamedList::go;
  std::cout << "go = " << r << " (want 3)" << std::endl;
  assert(r == 3);
  return 0;
}
