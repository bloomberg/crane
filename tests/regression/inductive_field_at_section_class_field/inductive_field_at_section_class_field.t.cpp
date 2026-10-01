#include <cassert>
#include <inductive_field_at_section_class_field.h>

int main() {
  assert(std::holds_alternative<Nat::O>(
      InductiveFieldAtSectionClassField::run.v()));
  return 0;
}
