#include <binder_type_names_section_field.h>

#include <cassert>
#include <iostream>

int main() {
  assert(BinderTypeNamesSectionField::is_five);
  std::cout << "binder_type_names_section_field: ok" << std::endl;
  return 0;
}
