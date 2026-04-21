#include <imported_alias_qualification.h>

#include <cassert>
#include <iostream>

int main() {
  // entry should be None (empty_cell)
  auto result = entry;
  assert(!result.has_value());
  std::cout << "All imported_alias_qualification tests passed!" << std::endl;
  return 0;
}
