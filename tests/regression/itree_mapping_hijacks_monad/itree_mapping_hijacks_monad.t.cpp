#include <itree_mapping_hijacks_monad.h>

#include <cassert>

int main() {
  // twice (Ok 2) is Ok 4.
  auto r = ItreeMappingHijacksMonad::use(Nat::s(Nat::s(Nat::o())));
  assert(std::holds_alternative<Err<Nat>::Ok>(r.v()));
  return 0;
}
