// WIP: this test does not build yet.
//
// A constructor field holding the inductive under an `option`
// (`N : option c -> c`) is stored as `shared_ptr<optional<c>>` but the
// generated pattern match calls `.has_value()` on the pointer.
#include "recursive_under_option.h"

#include <cassert>
#include <iostream>

int main() {
  assert(RecursiveUnderOption::go == 1000);
  std::cout << "recursive_under_option: go = " << RecursiveUnderOption::go << " PASSED" << std::endl;
  return 0;
}
