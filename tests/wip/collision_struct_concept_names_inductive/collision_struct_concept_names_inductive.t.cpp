#include <cassert>
#include <collision_struct_concept_names_inductive.h>

int main() {
  using M = CollisionStructConceptNamesInductive;
  assert(M::check);
  assert(M::blue);
  return 0;
}
