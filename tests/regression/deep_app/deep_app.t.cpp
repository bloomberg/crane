#include <deep_app.h>

#include <cassert>
#include <iostream>

int main() {
  // Build a deep list iteratively (loopified)
  auto l = DeepApp::build(10000u, DeepApp::mylist<unsigned int>::mynil());
  std::cout << "Built list of 10k elements" << std::endl;

  // map is recursive (not loopified by default).
  // Even if TMC produces an iterative version, the resulting list is
  // still 10k elements deep.
  auto mapped = DeepApp::map_id(l);
  std::cout << "Mapped list" << std::endl;

  auto h = DeepApp::head_or_zero(mapped);
  std::cout << "head = " << h << std::endl;
  assert(h == 1u);

  std::cout << "All deep_app tests passed!" << std::endl;
  return 0;
}
