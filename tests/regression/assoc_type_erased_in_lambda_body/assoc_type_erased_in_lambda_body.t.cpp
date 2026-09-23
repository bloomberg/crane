#include <assoc_type_erased_in_lambda_body.h>
#include <cassert>
#include <variant>

int main() {
  // Instantiating the field is what makes the body and its signature meet.
  auto p = PointerV<IPZ>::int_to_ptr(Nat::o(), List<Nat>::nil());
  assert(std::holds_alternative<typename Nat::O>(p.first.v()));
  assert(std::holds_alternative<typename List<Nat>::Nil>(p.second.v()));
  AssocTypeErasedInLambdaBody::go(Nat::o());
  return 0;
}
