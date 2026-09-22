#include <hk_carrier_written_at_partial_app.h>

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

}  // namespace

int main() {
  auto es = List<Exp0<Nat>>::cons(Exp0<Nat>::var(nat(3)),
                                  List<Exp0<Nat>>::nil());
  const Phi<Nat> out =
      HkCarrierWrittenAtPartialApp::on_phi(Phi<Nat>::phi0(std::move(es)));
  const auto &[l] = out;
  const auto &c0 = std::get<List<Exp0<Nat>>::Cons>(l.v());
  assert(to_unsigned(std::get<Exp0<Nat>::Var>(c0.a.v()).t) == 4);
  return 0;
}
