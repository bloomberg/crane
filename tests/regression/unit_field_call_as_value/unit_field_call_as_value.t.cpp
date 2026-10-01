#include <unit_field_call_as_value.h>

#include <cassert>
#include <iostream>

int main() {
  assert(UnitFieldCallAsValue::is_three);
  std::cout << "unit_field_call_as_value: ok" << std::endl;
  return 0;
}
