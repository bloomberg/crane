#include <tfunctor_record_list_field.h>

#include <cassert>
#include <iostream>

int main() {
  // tfmap S over the bundle adds one to each of [1; 2].
  assert(TfunctorRecordListField::is_five);
  std::cout << "tfunctor_record_list_field: ok" << std::endl;
  return 0;
}
