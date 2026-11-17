// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <interp_state_dict.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using R = std::pair<uint64_t, uint64_t>;
using T = Itree<crane::obj, R>;
using TF = ItreeF<crane::obj, R, T>;

// Run a tree with no events to its result.
static R run(T t) {
  while (true) {
    const auto &o = t.observe();
    if (auto *r = std::get_if<TF::RetF>(&o.v())) return r->r;
    t = std::get<TF::TauF>(o.v()).t;
  }
}

int main() {
  // n ticks then a read: the final state and the value read are both n.
  for (uint64_t n : {0, 1, 5, 1000}) {
    R r = run(InterpStateDict::run(n));
    assert(r.first == n && r.second == n);
  }
  std::cout << "interp_state_dict: ok\n";
  return 0;
}
