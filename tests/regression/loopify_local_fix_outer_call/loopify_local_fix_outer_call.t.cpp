// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
// testing of Crane.
#include <loopify_local_fix_outer_call.h>

#include <cstdint>
#include <iostream>
#include <vector>

#define M LoopifyLocalFixOuterCall

static std::vector<uint64_t> to_vector(const List<uint64_t> &l) {
  std::vector<uint64_t> out;
  const List<uint64_t> *cur = &l;
  while (auto *c = std::get_if<List<uint64_t>::Cons>(&cur->v())) {
    out.push_back(c->a);
    cur = c->l.get();
  }
  return out;
}

int main() {
  int fails = 0;
  auto l = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  // g [1; 2] = go [1; 2] [] = go [2] (1 :: g [2]) = [2; 2], as g [2] = [2].
  auto r = M::g(l);
  if (!(to_vector(r) == std::vector<uint64_t>{2, 2})) { std::cout << "FAIL: g [1; 2]" << std::endl; ++fails; }
  auto r3 = M::g(List<uint64_t>::cons(3, List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()))));
  // g [3; 1; 2] = go [3; 1; 2] [] = 2 :: g [1; 2]: go keeps only its last cons.
  if (!(to_vector(r3) == std::vector<uint64_t>{2, 2, 2})) { std::cout << "FAIL: g [3; 1; 2]" << std::endl; ++fails; }

  if (fails == 0) std::cout << "All loopify_local_fix_outer_call tests passed!" << std::endl;
  return fails;
}
