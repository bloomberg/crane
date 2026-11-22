#include <boxed_fields_match_arg_obj.h>

#include <cassert>
#include <iostream>

int main() {
  auto a = BoxedFieldsMatchArgObj::count(0);
  auto b = BoxedFieldsMatchArgObj::count(3);
  std::cout << "count 0 = " << a << ", count 3 = " << b << std::endl;
  assert(a == 0);
  assert(b == 1);
  return 0;
}
