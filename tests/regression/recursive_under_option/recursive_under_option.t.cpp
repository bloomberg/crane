// A constructor field holding the inductive under an [option]
// ([N : option c -> c]) is stored as [shared_ptr<optional<c>>].  The pattern
// match must dereference the pointer before testing [has_value()].
#include "recursive_under_option.h"

#include <cassert>
#include <iostream>

int main() {
  assert(RecursiveUnderOption::go == 1000);
  std::cout << "recursive_under_option: go = " << RecursiveUnderOption::go << " PASSED" << std::endl;
  return 0;
}
