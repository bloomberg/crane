#include <interp_chain_perf.h>

#include <cassert>
#include <chrono>
#include <iostream>

static Nat mk(int k) { Nat n = Nat::o(); for (int i = 0; i < k; i++) n = Nat::s(n); return n; }
static int to_int(const Nat &n) {
  int k = 0; const Nat *p = &n;
  while (auto *s = std::get_if<Nat::S>(&p->v())) { k++; p = s->a0.get(); }
  return k;
}

int main() {
  auto t0 = std::chrono::steady_clock::now();
  auto r = InterpChainPerf::drive(mk(100000), InterpChainPerf::run_n(mk(200)));
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  assert(r.has_value() && to_int(*r) == 200);
  std::cout << "interp_chain_perf: n=200 in " << secs << "s" << std::endl;
  assert(secs < 2.0);
  return 0;
}
