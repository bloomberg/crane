#include <nested_custom_ctor_field_type.h>

#include <cassert>

int main() {
  auto r = NestedCustomCtorFieldType::run;

  (void)r;

  return 0;
}
