#include <cassert>
#include <bind_continuation_monad_element.h>

int main() {
  const auto &r = BindContinuationMonadElement::run;
  assert(std::holds_alternative<typename EOU<List<bool>>::Ok>(r.v()));
  const auto &[l] = std::get<typename EOU<List<bool>>::Ok>(r.v());
  assert(std::holds_alternative<typename List<bool>::Cons>(l.v()));
  const auto &[x, rest] = std::get<typename List<bool>::Cons>(l.v());
  assert(!x);
  assert(std::holds_alternative<typename List<bool>::Cons>(rest->v()));
  const auto &[y, rest2] = std::get<typename List<bool>::Cons>(rest->v());
  assert(y);
  assert(std::holds_alternative<typename List<bool>::Nil>(rest2->v()));
  return 0;
}
