#include <option_let_none_bug.h>

#include <cassert>
#include <iostream>

int main() {
  using OLNB = OptionLetNoneBug;

  auto result = OLNB::bug;
  std::cout << "bug.has_value() = " << result.has_value() << std::endl;
  assert(!result.has_value());

  std::cout << "All option_let_none_bug tests passed!" << std::endl;
  return 0;
}
