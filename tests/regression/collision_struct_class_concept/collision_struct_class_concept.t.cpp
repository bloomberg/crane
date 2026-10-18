#include <cassert>
#include <collision_struct_class_concept.h>

int main() {
  assert(check);
  assert(std::holds_alternative<Ident::Global>(to_ident(Nat::o()).v()));
  return 0;
}
