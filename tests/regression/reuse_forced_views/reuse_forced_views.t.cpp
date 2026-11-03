// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <reuse_forced_views.h>

#include <cassert>
#include <cstdio>
#include <string>
#include <utility>

using M = ReuseForcedViews;
using T = M::tree;
using Q = List<T>;
using P = List<std::pair<std::uint64_t, std::uint64_t>>;

static std::string show(const T &t) {
  if (std::holds_alternative<T::Leaf>(t.v())) return "L";
  const auto &n = std::get<T::Node>(t.v());
  return "N" + std::to_string(n.a0) + "(" + show(*n.a1) + "," + show(*n.a2) + ")";
}

static std::string show(const Q &q) {
  std::string out;
  for (const Q *p = &q; std::holds_alternative<Q::Cons>(p->v());) {
    const auto &c = std::get<Q::Cons>(p->v());
    out += show(c.a) + ";";
    p = c.l.get();
  }
  return out;
}

static T node(std::uint64_t x) { return T::node(x, T::leaf(), T::leaf()); }

static P pairs(std::initializer_list<std::pair<std::uint64_t, std::uint64_t>> xs) {
  P out = P::nil();
  for (auto it = std::rbegin(xs); it != std::rend(xs); ++it) out = P::cons(*it, std::move(out));
  return out;
}

static std::string opt(const std::optional<std::uint64_t> &o) { return o ? std::to_string(*o) : "-"; }

template <typename L> static std::string show_combined(const L &l) {
  std::string out;
  for (const L *p = &l; std::holds_alternative<typename L::Cons>(p->v());) {
    const auto &c = std::get<typename L::Cons>(p->v());
    out += std::to_string(c.a.first) + ":" + opt(c.a.second.first) + "/" + opt(c.a.second.second) + ";";
    p = c.l.get();
  }
  return out;
}

int main() {
  // A match on a tree the cursor's borrowed cell holds.
  assert(show(M::carry(Q::nil(), T::leaf())) == "");
  assert(show(M::carry(Q::nil(), node(1))) == "N1(L,L);");
  assert(show(M::carry(Q::cons(node(1), Q::nil()), node(2))) == "L;N2(N1(L,L),L);");
  {
    Q shared = Q::cons(node(3), Q::cons(T::leaf(), Q::nil()));
    Q r = M::carry(Q::cons(node(1), shared), node(2));
    assert(show(r) == "L;L;N3(N2(N1(L,L),L),L);");
    assert(show(shared) == "N3(L,L);L;");
  }
  // An entered fixpoint passing on the tail of the cell its turn took apart.
  assert(show_combined(M::combine(pairs({{1, 10}, {3, 30}}), pairs({{1, 11}, {2, 22}}))) ==
         "1:10/11;2:-/22;3:30/-;");
  assert(show_combined(M::combine(pairs({{1, 10}, {2, 20}}), pairs({{3, 33}}))) == "1:10/-;2:20/-;3:-/33;");
  assert(show_combined(M::combine(pairs({{5, 50}}), pairs({{1, 11}, {2, 22}, {5, 55}}))) ==
         "1:-/11;2:-/22;5:50/55;");
  std::printf("reuse_forced_views: ok\n");
  return 0;
}
