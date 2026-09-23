#include <tfunctor_record_field_carrier.h>
#include <cassert>

static Nat nat_of(int n) {
  Nat r = Nat::o();
  for (int i = 0; i < n; i++) r = Nat::s(r);
  return r;
}

static int int_of(const Nat &n) {
  int c = 0;
  Nat cur = n;
  while (std::holds_alternative<typename Nat::S>(cur.v())) {
    const auto &[p] = std::get<typename Nat::S>(cur.v());
    cur = *p;
    c++;
  }
  return c;
}

int main() {
  auto succ = [](Nat n) { return Nat::s(n); };

  // The top-level composed carrier: already correct, kept as the control.
  auto o = use_option(succ, std::optional<Exp<Nat>>(
                                   Exp<Nat>::e_leaf(nat_of(2))));
  assert(o.has_value());
  assert(int_of(std::get<typename Exp<Nat>::E_leaf>(o->v()).a0) == 3);

  // The same carrier through a record field.
  glob<Nat> g{nat_of(1),
                 std::optional<Exp<Nat>>(Exp<Nat>::e_leaf(nat_of(2))),
                 List<Exp<Nat>>::cons(Exp<Nat>::e_leaf(nat_of(3)),
                                         List<Exp<Nat>>::nil())};
  glob<Nat> h = use_glob(succ, g);
  assert(int_of(h.g_name) == 2);
  assert(h.g_exp.has_value());
  assert(int_of(std::get<typename Exp<Nat>::E_leaf>(h.g_exp->v()).a0) == 3);
  const auto &[hd, tl] = std::get<typename List<Exp<Nat>>::Cons>(h.g_anns.v());
  assert(int_of(std::get<typename Exp<Nat>::E_leaf>(hd.v()).a0) == 4);
  return 0;
}
