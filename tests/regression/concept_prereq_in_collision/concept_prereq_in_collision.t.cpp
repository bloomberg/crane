#include <cassert>
#include <concept_prereq_in_collision.h>

int main() {
  assert(check);
  assert(std::holds_alternative<Ident::Global>(to_ident(Nat::o()).v()));
  AstLike::key k = key_twice(first_key);
  (void)k;
  assert(twice_first);
  return 0;
}
