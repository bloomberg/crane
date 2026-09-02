#include <hkt_curried_pure_arity.h>
#include <cassert>

int main() {
  auto r = HktCurriedPureArity::run(std::optional<Nat>(Nat::o()),
                                    std::optional<Nat>(Nat::s(Nat::o())));
  assert(r.has_value());
  return 0;
}
