#include <pattern_lambda_binder_over_erased.h>

#include <cassert>

namespace {

Nat nat(unsigned n) {
  Nat acc = Nat::o();
  for (unsigned i = 0; i < n; ++i) acc = Nat::s(std::move(acc));
  return acc;
}

unsigned to_unsigned(const Nat &n) {
  unsigned c = 0;
  const Nat *cur = &n;
  while (std::holds_alternative<Nat::S>(cur->v())) {
    cur = std::get<Nat::S>(cur->v()).a0.get();
    ++c;
  }
  return c;
}

/// The list [(0, Var 3); (1, Lit 7)], which exercises both [exp] constructors:
/// [bump] must reach the [Var] payload and leave the [Lit] index alone.
Phi<Nat> sample() {
  using Elem = std::pair<Nat, Exp0<Nat>>;
  auto es = List<Elem>::cons(
      Elem{nat(0), Exp0<Nat>::var(nat(3))},
      List<Elem>::cons(Elem{nat(1), Exp0<Nat>::lit(nat(7))},
                       List<Elem>::nil()));
  return Phi<Nat>::phi0(std::move(es));
}

}  // namespace

int main() {
  const Phi<Nat> out = PatternLambdaBinderOverErased::on_phi(sample());
  const auto &[es] = out;

  const auto &c0 = std::get<List<std::pair<Nat, Exp0<Nat>>>::Cons>(es.v());
  assert(to_unsigned(c0.a.first) == 0);
  assert(to_unsigned(std::get<Exp0<Nat>::Var>(c0.a.second.v()).t) == 4);

  const auto &c1 =
      std::get<List<std::pair<Nat, Exp0<Nat>>>::Cons>(c0.l->v());
  assert(to_unsigned(c1.a.first) == 1);
  assert(to_unsigned(std::get<Exp0<Nat>::Lit>(c1.a.second.v()).n) == 7);

  return 0;
}
