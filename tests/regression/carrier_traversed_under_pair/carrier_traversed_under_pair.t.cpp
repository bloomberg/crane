#include <cassert>
#include <carrier_traversed_under_pair.h>

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
  // b_code : list (nat * Exp nat), traversed in the pair's second component.
  auto e = Exp<Nat>::e_leaf(nat_of(3));
  List<std::pair<std::optional<Nat>, Exp<Nat>>> code =
      List<std::pair<std::optional<Nat>, Exp<Nat>>>::cons(std::make_pair(std::optional<Nat>(nat_of(7)), e),
                                           List<std::pair<std::optional<Nat>, Exp<Nat>>>::nil());
  blk<Nat> b{nat_of(1), code};

  blk<bool> r = use_blk([](Nat n) { return nat_to_int(n) == 3; }, b);

  assert(nat_to_int(r.b_id) == 1);
  const auto &[p, ps] =
      std::get<typename List<std::pair<std::optional<Nat>, Exp<bool>>>::Cons>(r.b_code.v());
  assert(p.first.has_value() && nat_to_int(*p.first) == 7);
  const auto &leaf = std::get<typename Exp<bool>::E_leaf>(p.second.v());
  assert(leaf.a0 == true);
  return 0;
}
