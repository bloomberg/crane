#include <captured_record_copied_per_event.h>

#include <cassert>
#include <chrono>
#include <iostream>

using C = CapturedRecordCopiedPerEvent;

static Nat mk_nat(int k) { Nat n = Nat::o(); for (int i = 0; i < k; i++) n = Nat::s(n); return n; }
static int to_int(const Nat &n) {
  int k = 0; const Nat *p = &n;
  while (auto *s = std::get_if<Nat::S>(&p->v())) { k++; p = s->a0.get(); }
  return k;
}

int main() {
  const int n = 20, k = 400;
  auto t0 = std::chrono::steady_clock::now();
  auto r = C::run(mk_nat(100000), C::steps(mk_nat(n), mk_nat(k), C::mk(mk_nat(1)), Nat::o()));
  double secs = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  assert(r.has_value() && to_int(*r) == n);
  std::cout << "captured_record_copied_per_event: " << secs << "s" << std::endl;
  // Sharing the captured block: ~0.4s at -O0.  Copying it: ~9.4s.
  assert(secs < 3.0);
  return 0;
}
