#include <mutual_tmc_loopify.h>
#include <cassert>

static Nat of_int(int n) {
  Nat r = Nat::o();
  for (int i = 0; i < n; ++i) r = Nat::s(std::move(r));
  return r;
}

int main() {
  // Deep enough that a genuinely recursive `evens` blows the stack.
  MutualTmcLoopify::mylist l = MutualTmcLoopify::evens(of_int(200000));
  assert(std::holds_alternative<typename MutualTmcLoopify::mylist::Mcons>(l.v()));
  return 0;
}
