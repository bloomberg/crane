#include <alias_carrier_under_map_lambda.h>
#include <cassert>

static Nat nat_of(int n) {
  Nat r = Nat::o();
  for (int i = 0; i < n; i++) r = Nat::s(r);
  return r;
}

int main() {
  auto is_two = [](Nat n) {
    return std::holds_alternative<typename Nat::S>(n.v()) &&
           std::holds_alternative<typename Nat::S>(
               std::get<typename Nat::S>(n.v()).a0->v()) &&
           std::holds_alternative<typename Nat::O>(
               std::get<typename Nat::S>(
                   std::get<typename Nat::S>(n.v()).a0->v())
                   .a0->v());
  };

  texp<Nat> fn{nat_of(2), Exp<Nat>::e_leaf(nat_of(2))};
  auto args = List<std::pair<texp<Nat>, Nat>>::cons(
      std::make_pair(texp<Nat>{nat_of(2), Exp<Nat>::e_leaf(nat_of(1))},
                     nat_of(7)),
      List<std::pair<texp<Nat>, Nat>>::nil());

  Instr<bool> r = use_instr(is_two, Instr<Nat>::i_call(fn, args));

  const auto &c = std::get<typename Instr<bool>::I_call>(r.v());
  assert(c.a0.first == true);
  // The mapped element: the carrier under the List.map lambda.
  const auto &[hd, tl] = std::get<typename List<std::pair<texp<bool>, Nat>>::Cons>(
      c.a1.v());
  assert(hd.first.first == true);
  assert(std::get<typename Exp<bool>::E_leaf>(hd.first.second.v()).a0 == false);
  return 0;
}
