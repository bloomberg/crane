// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <mrec_fact.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using T = Itree<crane::obj, uint64_t>;
using TF = ItreeF<crane::obj, uint64_t, T>;

// Run a tree with no events to its result, counting its taus.
static uint64_t run(T t, long &taus) {
  while (true) {
    const auto &o = t.observe();
    if (auto *r = std::get_if<TF::RetF>(&o.v())) return r->r;
    auto *u = std::get_if<TF::TauF>(&o.v());
    assert(u && "a tree with no events reached an event");
    ++taus;
    t = u->t;
  }
}

int main() {
  long taus = 0;
  assert(run(MrecFact::fact(UINT64_C(5)), taus) == 120);
  // One tau per handled call and one per return through the bind: the
  // interpreter's step count is part of the tree.
  long taus20 = 0;
  assert(run(MrecFact::fact(UINT64_C(20)), taus20) == UINT64_C(2432902008176640000));
  std::cout << "fact 5: " << taus << " taus, fact 20: " << taus20 << " taus\n";
  std::cout << "mrec_fact: ok\n";
  return 0;
}
