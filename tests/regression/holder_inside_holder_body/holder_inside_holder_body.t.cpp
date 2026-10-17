#include <holder_inside_holder_body.h>

#include <cassert>
#include <iostream>

int main() {
  auto id = &HolderInsideHolderBody::stacked_id<HolderInsideHolderBody::noE>;
  assert(id != nullptr);
  std::cout << "holder_inside_holder_body: ok" << std::endl;
  return 0;
}
