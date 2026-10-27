// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <loopify_adopted_fix_alias_result.h>

#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>

using M = LoopifyAdoptedFixAliasResult;

// The keys and values [merged n] holds, as a std::map does it.
static std::map<uint64_t, uint64_t> expected(uint64_t n) {
  std::map<uint64_t, uint64_t> m;
  for (uint64_t i = 0; i < n; ++i) {
    m[2 * i] += i;
    m[3 * i] += i;
  }
  return m;
}

static void check(uint64_t n) {
  auto want = expected(n);
  auto it = want.begin();
  const List<std::pair<uint64_t, uint64_t>> *l = nullptr;
  M::t<uint64_t> got = M::merged(n);
  for (l = &got; std::holds_alternative<List<std::pair<uint64_t, uint64_t>>::Cons>(l->v());) {
    const auto &c = std::get<List<std::pair<uint64_t, uint64_t>>::Cons>(l->v());
    assert(it != want.end());
    assert(c.a.first == it->first && c.a.second == it->second);
    ++it;
    l = c.l.get();
  }
  assert(it == want.end());
  assert(M::sum(got) == n * (n - 1));
}

int main() {
  check(0);
  check(1);
  check(7);
  // Deep enough that the recursion it replaced would have exhausted the stack.
  check(200000);
  std::cout << "loopify_adopted_fix_alias_result: ok\n";
  return 0;
}
