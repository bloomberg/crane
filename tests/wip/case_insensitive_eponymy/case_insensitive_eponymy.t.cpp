#include <case_insensitive_eponymy.h>

#include <cassert>

int main() {
  // size of a one-block cfg is 1, then Other.size gives 2.
  assert(CaseInsensitiveEponymy::use(cfg<Nat>{Nat::o(), List::cons(Nat::o(), List::nil<Nat>())})
         == Nat::s(Nat::s(Nat::o())));
  return 0;
}
