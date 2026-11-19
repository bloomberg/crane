// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "lazy_direct_layer.h"

#include <iostream>
#include <stdexcept>
#include <utility>

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

#define ASSERT(...) aSsErT(!(__VA_ARGS__), #__VA_ARGS__, __LINE__);

using M = LazyDirectLayer;
using tree = M::tree;
using F = M::treeF<tree>;

// The layer is one word naming its own block, so the cell holds an evaluated
// one in its word.
static_assert(sizeof(tree::variant_t) == sizeof(void *));
static_assert(crane::word_detail::is_word_owner<tree::variant_t>());
static_assert(sizeof(tree) == sizeof(void *));

// The layer a tree's cell holds, by reference into the cell.
static const F &layer(const tree &t) { return crane::get<tree::Go>(t.v()).observe; }
static uint64_t ret_of(const tree &t) { return crane::get<F::RetF>(layer(t).v()).r; }

int main() {
  // Evaluated layers: copies share, a move leaves nothing behind.
  tree r = M::Ret(7);
  tree alias = r;
  ASSERT(ret_of(alias) == 7);
  ASSERT(&layer(r) == &layer(r));
  tree moved = std::move(alias);
  ASSERT(ret_of(moved) == 7);
  bool threw = false;
  try {
    (void)layer(alias);
  } catch (const std::logic_error &) {
    threw = true;
  }
  ASSERT(threw);

  // A nullary alternative is an odd word, held the same way.
  ASSERT(crane::holds_alternative<F::StopF>(layer(M::Stop).v()));
  tree stop = M::Stop;
  ASSERT(crane::holds_alternative<F::StopF>(layer(stop).v()));
  ASSERT(!M::run(10, stop).has_value());

  // A suspended layer runs once, whichever alias forces it.
  int runs = 0;
  tree susp = tree::lazy_([&]() -> tree::Go {
    ++runs;
    return {F::tauf(r)};
  });
  tree susp2 = susp;
  const tree &t1 = crane::get<F::TauF>(layer(susp).v()).t;
  const tree &t2 = crane::get<F::TauF>(layer(susp2).v()).t;
  ASSERT(runs == 1);
  ASSERT(&t1 == &t2);
  ASSERT(ret_of(t1) == 7);

  // A thunk producing an evaluated tree: its value is adopted.
  tree d = tree::lazy_([&]() -> tree { return M::Ret(8); });
  ASSERT(ret_of(d) == 8);
  tree d2 = tree::lazy_([&]() -> tree { return r; });
  ASSERT(ret_of(d2) == 7);

  // A long chain of delegations to evaluated trees.
  tree chain = r;
  for (int i = 0; i < 200000; ++i) {
    tree prev = chain;
    chain = tree::lazy_([prev]() -> tree { return prev; });
  }
  ASSERT(ret_of(chain) == 7);

  // A thunk that throws is left as it was and forced again.
  bool fail = true;
  tree thr = tree::lazy_([&]() -> tree::Go {
    if (fail)
      throw std::runtime_error("not yet");
    return {F::retf(3)};
  });
  threw = false;
  try {
    (void)layer(thr);
  } catch (const std::runtime_error &) {
    threw = true;
  }
  ASSERT(threw);
  fail = false;
  ASSERT(ret_of(thr) == 3);

  // A thunk that forces its own cell.
  tree *self = nullptr;
  tree loop = tree::lazy_([&]() -> tree::Go {
    (void)self->v();
    return {F::retf(1)};
  });
  self = &loop;
  threw = false;
  try {
    (void)layer(loop);
  } catch (const std::logic_error &) {
    threw = true;
  }
  ASSERT(threw);

  // Generated corecursion: suspended taus, evaluated rets and visits.
  ASSERT(M::run(1000, M::taus(500, 4)) == std::optional<uint64_t>(4));
  ASSERT(!M::run(10, M::taus(500, 4)).has_value());
  // ask 3 answers 3, 2, 1 to the events 2, 1, 0.
  ASSERT(M::run(100, M::ask(3, 0)) == std::optional<uint64_t>(6));
  tree shared = M::taus(1000, 5);
  ASSERT(M::run(2000, shared) == std::optional<uint64_t>(5));
  ASSERT(M::run(2000, shared) == std::optional<uint64_t>(5));

  // Boxed into crane::obj as its counted word, evaluated or suspended.
  crane::obj o(r);
  crane::obj o2 = o;
  ASSERT(ret_of(*crane::any_cast<tree>(&o2)) == 7);
  crane::obj os(susp);
  ASSERT(ret_of(crane::get<F::TauF>(layer(*crane::any_cast<tree>(&os)).v()).t) == 7);

  return testStatus;
}
