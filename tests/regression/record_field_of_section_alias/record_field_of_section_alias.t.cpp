#include <cassert>
#include <record_field_of_section_alias.h>

int main() {
  assert(std::holds_alternative<Nat::O>(RecordFieldOfSectionAlias::run.v()));
  return 0;
}
