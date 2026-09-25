#include <cassert>
#include <section_definition_instantiated_outside.h>

int main() {
  assert(std::holds_alternative<Nat::O>(SectionDefinitionInstantiatedOutside::run.v()));
  return 0;
}
