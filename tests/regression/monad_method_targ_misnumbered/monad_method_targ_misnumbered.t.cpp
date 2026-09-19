#include "monad_method_targ_misnumbered.h"
#include <cassert>
#include <variant>

int main() {
  auto r = MonadMethodTargMisnumbered::use(
      List<Nat>::cons(Nat::s(Nat::o()), List<Nat>::nil()));
  assert(r.has_value());
  assert(std::holds_alternative<typename Nat::S>(r.value().v()));
  return 0;
}
