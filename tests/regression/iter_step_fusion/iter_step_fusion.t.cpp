// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#define CRANE_COUNT_TAKES 1
#include <iter_step_fusion.h>

#include <cassert>
#include <cstdint>
#include <iostream>
#include <string>

using F = IterStepFusion;
using T = F::itree<uint64_t>;
using TF = F::itreeF<uint64_t, T>;

// [taus] taus, then for each of [events] an event and [taus] more taus,
// ending in [ret v].
static T input(int taus, int events, uint64_t v) {
  T t = T::go(TF::retf(v));
  for (int e = 0; e < events; ++e) {
    for (int i = 0; i < taus; ++i) t = T::go(TF::tauf(t));
    T rest = t;
    t = T::go(TF::visf(uint64_t(e), [rest](uint64_t) { return rest; }));
  }
  for (int i = 0; i < taus; ++i) t = T::go(TF::tauf(t));
  return t;
}

// The tree as its observations: T a tau, V<e> an event (answered with 0),
// R<v> the result.  The driver of an interaction tree walks it one node at a
// time, so the specialized interpreter must build the same tree node for
// node, taus included, not merely reach the same result.
static std::string walk(T t) {
  std::string s;
  while (true) {
    const auto &o = F::observe<uint64_t>(t);
    if (auto *r = std::get_if<TF::RetF>(&o.v())) {
      return s + "R" + std::to_string(r->r);
    } else if (auto *u = std::get_if<TF::TauF>(&o.v())) {
      s += "T";
      t = u->t;
    } else {
      const auto &v = std::get<TF::VisF>(o.v());
      s += "V" + std::to_string(v.e);
      t = v.k(0);
    }
  }
}

int main() {
  auto h = [](uint64_t e) { return T::go(TF::retf(e + 1)); };
  for (int taus : {0, 1, 7, 1000})
    for (int events : {0, 1, 3}) {
      T a = input(taus, events, 42), b = input(taus, events, 42);
      std::size_t t0 = crane::pool_detail::takes;
      std::string plain = walk(F::interp_by_name<uint64_t>(h, a));
      std::size_t t1 = crane::pool_detail::takes;
      std::string fused = walk(F::interp<uint64_t>(h, b));
      std::size_t t2 = crane::pool_detail::takes;
      assert(plain == fused);
      if (taus == 1000) {
        std::cout << events << " events: allocations unspecialized " << (t1 - t0)
                  << ", specialized " << (t2 - t1) << "\n";
        assert(t2 - t1 < t1 - t0);
      }
    }
  std::cout << "iter_step_fusion: ok\n";
  return 0;
}
