// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "union_find.h"

#include <cstdint>
#include <iostream>
#include <numeric>
#include <utility>
#include <vector>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;

    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

namespace {

struct Step {
  bool is_union;
  uint64_t x, y;
};

List<Op> to_ops(const std::vector<Step> &steps) {
  List<Op> ops = List<Op>::nil();
  for (auto it = steps.rbegin(); it != steps.rend(); ++it) {
    ops = List<Op>::cons(it->is_union ? Op::Union_(it->x, it->y)
                                      : Op::same(it->x, it->y),
                         std::move(ops));
  }
  return ops;
}

std::vector<bool> to_vector(const List<bool> &l) {
  std::vector<bool> out;
  const List<bool> *p = &l;
  while (const auto *c = std::get_if<List<bool>::Cons>(&p->v())) {
    out.push_back(c->a);
    p = c->l.get();
  }
  return out;
}

// Reference answers from a plain quadratic relabelling, independent of both
// extracted versions.
std::vector<bool> reference(uint64_t n, const std::vector<Step> &steps) {
  std::vector<uint64_t> label(n);
  std::iota(label.begin(), label.end(), 0);
  std::vector<bool> out;
  for (const Step &s : steps) {
    if (!s.is_union) {
      out.push_back(label[s.x] == label[s.y]);
    } else if (label[s.x] != label[s.y]) {
      uint64_t from = label[s.y], to = label[s.x];
      for (uint64_t &l : label) {
        if (l == from) l = to;
      }
    }
  }
  return out;
}

// Runs both extracted versions on [steps] and checks them against each other
// and against [reference].
void check(const char *name, uint64_t n, const std::vector<Step> &steps) {
  List<Op> ops = to_ops(steps);
  std::vector<bool> st = to_vector(UnionFind::union_find_ST(n, ops));
  std::vector<bool> fun = to_vector(UnionFind::union_find_fun(n, ops));
  std::vector<bool> ref = reference(n, steps);
  ASSERT(st == fun);
  ASSERT(st == ref);
  uint64_t yes = 0;
  for (bool b : st) yes += b;
  std::cout << name << ": n = " << n << ", " << steps.size()
            << " operations, " << st.size() << " queries, " << yes
            << " connected" << (st == fun && st == ref ? " PASSED" : " FAILED")
            << std::endl;
}

} // namespace

int main() {
  // A small hand-checked run.
  {
    std::vector<Step> steps = {
        {true, 1, 2},  {true, 3, 4},  {false, 1, 2}, {false, 1, 3},
        {true, 2, 3},  {false, 1, 4}, {false, 0, 9}, {true, 9, 0},
        {false, 0, 9}, {false, 5, 6}, {false, 4, 4}, {true, 4, 1},
        {false, 2, 3}};
    List<Op> ops = to_ops(steps);
    std::vector<bool> expected = {true,  false, true, false,
                                  true,  false, true, true};
    ASSERT(to_vector(UnionFind::union_find_ST(10, ops)) == expected);
    ASSERT(to_vector(UnionFind::union_find_fun(10, ops)) == expected);
    check("small", 10, steps);
  }

  // The pure structure is persistent: an old version keeps its answers.
  {
    uf s0 = empty_uf;
    uf s1 = union_fun(8, s0, 0, 1);
    uf s2 = union_fun(8, s1, 1, 2);
    uf s3 = union_fun(8, s2, 5, 6);
    ASSERT(same_fun(8, s3, 0, 2).first);
    ASSERT(same_fun(8, s3, 5, 6).first);
    ASSERT(!same_fun(8, s3, 2, 5).first);
    ASSERT(!same_fun(8, s1, 0, 2).first);
    ASSERT(same_fun(8, s1, 0, 1).first);
    ASSERT(!same_fun(8, s0, 0, 1).first);
    // find returns a root, which is its own root.
    auto [r, s4] = find_fun(8, s3, 2);
    ASSERT(find_fun(8, s4, r).first == r);
    ASSERT(find_fun(8, s4, 0).first == r);
    std::cout << "persistence: PASSED" << std::endl;
  }

  // One long chain: every element ends up in a single set.
  {
    const uint64_t n = 1000;
    std::vector<Step> steps;
    for (uint64_t i = 0; i + 1 < n; ++i) steps.push_back({true, i + 1, i});
    for (uint64_t i = 0; i < n; i += 7) steps.push_back({false, 0, i});
    check("chain", n, steps);
  }

  // A larger pseudo-random run, unions and queries interleaved.
  {
    const uint64_t n = 1000;
    uint64_t seed = 0x9e3779b97f4a7c15ULL;
    auto next = [&seed]() {
      seed = seed * 6364136223846793005ULL + 1442695040888963407ULL;
      return seed >> 33;
    };
    std::vector<Step> steps;
    for (int i = 0; i < 5000; ++i) {
      bool is_union = next() % 5 < 2;
      steps.push_back({is_union, next() % n, next() % n});
    }
    check("random", n, steps);
  }

  return testStatus;
}
