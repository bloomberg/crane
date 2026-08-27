// A record field whose type is a `Type`-valued `Fixpoint` applied to a
// literal (`ty 2`, i.e. a nested pair) is projected twice.
#include "type_level_fixpoint_record_field.h"

#include <cassert>
#include <iostream>

int main() {
  assert(TypeLevelFixpointRecordField::go == 1);
  std::cout << "type_level_fixpoint_record_field: go = " << TypeLevelFixpointRecordField::go << " PASSED" << std::endl;
  return 0;
}
