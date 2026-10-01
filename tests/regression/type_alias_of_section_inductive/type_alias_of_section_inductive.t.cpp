#include <cassert>
#include <type_alias_of_section_inductive.h>

int main() {
  assert(std::holds_alternative<Nat::O>(TypeAliasOfSectionInductive::run.v()));
  return 0;
}
