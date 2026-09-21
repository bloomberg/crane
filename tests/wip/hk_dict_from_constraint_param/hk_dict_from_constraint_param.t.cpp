#include <hk_dict_from_constraint_param.h>

#include <cassert>
#include <variant>

int main() {
  auto boxes = List<box<Nat>>::cons(box<Nat>{Nat::o()}, List<box<Nat>>::nil());
  holder<Nat, List<Nat>> m{boxes, List<Nat>::nil()};
  auto r = HkDictFromConstraintParam::run(m);
  assert(std::holds_alternative<List<box<Nat>>::Cons>(r.h_boxes.v()));
  return 0;
}
