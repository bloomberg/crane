#include <tfunctor_record_option_field.h>

#include <cassert>
#include <iostream>

int main() {
  // tfmap S: g_typ 1 -> 2, g_exp Some (Lit 2) -> Some (Lit 3).
  assert(TfunctorRecordOptionField::is_five);
  std::cout << "tfunctor_record_option_field: ok" << std::endl;
  return 0;
}
