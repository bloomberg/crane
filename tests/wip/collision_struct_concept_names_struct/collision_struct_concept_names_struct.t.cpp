#include <collision_struct_concept_names_struct.h>
#include <cassert>
#include <iostream>

int main() {
  std::cout << CollisionStructConceptNamesStruct::sz << std::endl;
  assert(CollisionStructConceptNamesStruct::sz == 6);
  return 0;
}
