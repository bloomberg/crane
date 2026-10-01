#include <coinductive_node_sharing.h>

#include <cassert>
#include <chrono>
#include <iostream>
#include <variant>

using C = CoinductiveNodeSharing;
using T = Itree<C::voidE, uint64_t>;
using F = ItreeF<C::voidE, uint64_t, T>;

// Walks [t] to its [Ret], keeping [t] itself alive: every node forced on the
// way stays reachable from it until the caller drops it.
static uint64_t run(const T &t, uint64_t &steps) {
  const T *cur = &t;
  for (;;) {
    const F &o = cur->observe(); // a reference: no copy of the node
    if (auto *r = std::get_if<typename F::RetF>(&o.v()))
      return r->r;
    cur = &std::get<typename F::TauF>(o.v()).t;
    ++steps;
  }
}

int main() {
  const uint64_t k = 300000;
  auto t0 = std::chrono::steady_clock::now();
  uint64_t steps = 0, again = 0;
  {
    T t = C::count_to(k);
    assert(run(t, steps) == k);
    assert(steps >= k);
    // A second walk finds every step already forced, and every delegation
    // already pointing at its value.
    assert(run(t, again) == k && again == steps);
  } // dropping the whole forced chain must not recurse once per step
  double secs =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
  std::cout << "coinductive_node_sharing: " << steps << " steps, " << secs << "s"
            << std::endl;
  // Linear: about 6 s per million steps at -O0 on this machine.
  // A walk that re-traversed delegation chains would be quadratic.
  assert(secs < 15.0);
  return 0;
}
