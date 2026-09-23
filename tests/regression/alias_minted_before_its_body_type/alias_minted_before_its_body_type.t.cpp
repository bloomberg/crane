#include <alias_minted_before_its_body_type.h>
#include <cassert>

static Nat nat_of(int n) {
  Nat r = Nat::o();
  for (int i = 0; i < n; i++) r = Nat::s(r);
  return r;
}

static int nat_to_int(const Nat &n) {
  int c = 0;
  Nat m = n;
  while (std::holds_alternative<typename Nat::S>(m.v())) {
    c++;
    m = *std::get<typename Nat::S>(m.v()).a0;
  }
  return c;
}

int main() {
  List<boxed<Nat>> l = List<boxed<Nat>>::cons(
      std::make_pair(nat_of(5), Exp<Nat>::e_leaf(nat_of(3))),
      List<boxed<Nat>>::nil());

  List<boxed<bool>> r =
      use_boxedlist([](Nat n) { return nat_to_int(n) == 3; }, l);

  const auto &[p, ps] = std::get<typename List<boxed<bool>>::Cons>(r.v());
  assert(nat_to_int(p.first) == 5);
  assert(std::get<typename Exp<bool>::E_leaf>(p.second.v()).a0 == true);
  return 0;
}
