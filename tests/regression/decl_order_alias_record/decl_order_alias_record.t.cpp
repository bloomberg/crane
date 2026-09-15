#include <decl_order_alias_record.h>

#include <cassert>
#include <iostream>

int main() {
  // sample = {| code := [IGo 3; ICmp CEq; IStop]; nregs := 2 |}
  assert(sample_size == 3);
  assert(sample_regs == 2);
  std::cout << "All decl_order_alias_record tests passed!" << std::endl;
  return 0;
}
