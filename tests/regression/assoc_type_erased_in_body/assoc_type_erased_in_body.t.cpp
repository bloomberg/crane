#include <assoc_type_erased_in_body.h>
#include <cassert>
#include <variant>

int main() {
  // Instantiating the method is what makes the body and its signature meet.
  auto p = PointerV<IPZ>::null();
  assert(std::holds_alternative<typename Nat::O>(p.first.v()));
  assert(std::holds_alternative<typename List<Nat>::Nil>(p.second.v()));
  AssocTypeErasedInBody::go(Nat::o());
  return 0;
}
