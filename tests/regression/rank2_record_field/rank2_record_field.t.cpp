// A rank-2 record field ([forall A, list A -> nat]) stores a methodified
// function as a value; the reference becomes a method-calling lambda.
#include "rank2_record_field.h"

#include <cassert>
#include <iostream>

int main() {
  assert(Rank2RecordField::go == 3);
  std::cout << "rank2_record_field: go = " << Rank2RecordField::go << " PASSED" << std::endl;
  return 0;
}
