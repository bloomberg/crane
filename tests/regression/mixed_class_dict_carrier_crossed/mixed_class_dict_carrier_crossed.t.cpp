#include <mixed_class_dict_carrier_crossed.h>
#include <cassert>

static Nat nat_of(int n) {
  Nat r = Nat::o();
  for (int i = 0; i < n; i++) r = Nat::s(r);
  return r;
}

int main() {
  auto nonzero = [](Nat n) {
    return std::holds_alternative<typename Nat::S>(n.v());
  };

  modu<Nat> m{nat_of(4),
              List<Exp<Nat>>::cons(Exp<Nat>::e_leaf(nat_of(1)),
                                   List<Exp<Nat>>::nil()),
              List<Decl<Nat>>::cons(Decl<Nat>{nat_of(0)},
                                    List<Decl<Nat>>::nil())};

  modu<bool> r = use_modu(nonzero, m);

  // The Endo field between the two traversals: unchanged by endo = id.
  assert(std::holds_alternative<typename Nat::S>(r.m_tag.v()));
  // The traversal before the Endo dictionary.
  const auto &[e, es] = std::get<typename List<Exp<bool>>::Cons>(r.m_exps.v());
  assert(std::get<typename Exp<bool>::E_leaf>(e.v()).a0 == true);
  // The traversal after it: this is the one that used to take its sibling's
  // carrier.
  const auto &[d, ds] = std::get<typename List<Decl<bool>>::Cons>(r.m_decls.v());
  assert(d.a0 == false);
  return 0;
}
