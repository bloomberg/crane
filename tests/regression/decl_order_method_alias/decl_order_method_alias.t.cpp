#include <decl_order_method_alias.h>

#include <cassert>
#include <iostream>

int main() {
  // write_r [RU; RS 1; RU] 1 (RS 7) replaces the second register.
  assert(written_second == 7);
  // Writing past the end fails.
  assert(out_of_range);
  std::cout << "All decl_order_method_alias tests passed!" << std::endl;
  return 0;
}
