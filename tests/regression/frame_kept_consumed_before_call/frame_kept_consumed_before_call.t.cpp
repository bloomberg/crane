// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <frame_kept_consumed_before_call.h>

#include <cassert>
#include <cstdint>
#include <cstdio>
#include <vector>

using M = FrameKeptConsumedBeforeCall;
using Row = List<std::uint64_t>;
using Rows = List<Row>;
using Flat = std::vector<std::vector<std::uint64_t>>;

static Row row(std::vector<std::uint64_t> xs) {
  Row r = Row::nil();
  for (auto it = xs.rbegin(); it != xs.rend(); ++it) r = Row::cons(*it, r);
  return r;
}

static Rows rows(const Flat &xss) {
  Rows r = Rows::nil();
  for (auto it = xss.rbegin(); it != xss.rend(); ++it) r = Rows::cons(row(*it), r);
  return r;
}

static std::vector<std::uint64_t> flat_row(const Row &r) {
  std::vector<std::uint64_t> out;
  const Row *p = &r;
  while (std::holds_alternative<Row::Cons>(p->v())) {
    const auto &c = std::get<Row::Cons>(p->v());
    out.push_back(c.a);
    p = &*c.l;
  }
  return out;
}

static Flat flat(const Rows &r) {
  Flat out;
  const Rows *p = &r;
  while (std::holds_alternative<Rows::Cons>(p->v())) {
    const auto &c = std::get<Rows::Cons>(p->v());
    out.push_back(flat_row(c.a));
    p = &*c.l;
  }
  return out;
}

int main() {
  const Flat input = {{1, 2}, {3}, {4, 5}};
  const Flat paired = {{1, 2}, {1, 2, 0}, {3}, {3, 0}, {4, 5}};
  const Flat repeated = {{1, 2, 0}, {1, 2}, {1, 2, 0}, {1, 2}, {1, 2}};
  // Owned: the machine owns the rows the frames keep.
  assert(flat(M::pairs(10, rows(input))) == paired);
  assert(flat(M::again(10, rows(input))) == repeated);
  // Shared: the caller's rows survive.
  Rows shared = rows(input);
  assert(flat(M::pairs(10, shared)) == paired);
  assert(flat(M::again(10, shared)) == repeated);
  assert(flat(shared) == input);
  std::printf("frame_kept_consumed_before_call: ok\n");
  return 0;
}
