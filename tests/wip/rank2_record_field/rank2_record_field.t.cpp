// WIP: this test does not build yet.
//
// A record field with a rank-2 type (`forall A, list A -> nat`) emits a lambda
// body referring to an undeclared template parameter `_T1`.
#include "rank2_record_field.h"

#include <cassert>
#include <iostream>

int main() {
  assert(Rank2RecordField::go == 3);
  std::cout << "rank2_record_field: go = " << Rank2RecordField::go << " PASSED" << std::endl;
  return 0;
}
