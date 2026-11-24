#include <prim_string_pair_literal_copy_mode.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = PrimStringPairLiteralCopyMode::len(0);
  std::cout << "len = " << r << std::endl;
  assert(r == 2);
  assert(PrimStringPairLiteralCopyMode::first(1) == "ab");
  assert(PrimStringPairLiteralCopyMode::of_sum(0) == "cd");
  assert(PrimStringPairLiteralCopyMode::of_list(0) == "f");
  return 0;
}
