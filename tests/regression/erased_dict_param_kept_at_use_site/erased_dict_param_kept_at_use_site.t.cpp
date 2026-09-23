#include <erased_dict_param_kept_at_use_site.h>
#include <cassert>

static Nat nat_of(int n) {
  Nat r = Nat::o();
  for (int i = 0; i < n; i++) r = Nat::s(r);
  return r;
}

static int int_of(Nat n) {
  int i = 0;
  while (std::holds_alternative<typename Nat::S>(n.v())) {
    n = *std::get<typename Nat::S>(n.v()).a0;
    i++;
  }
  return i;
}

int main() {
  assert(int_of(ErasedDictParamKeptAtUseSite::go(nat_of(3))) == 67);
  return 0;
}
