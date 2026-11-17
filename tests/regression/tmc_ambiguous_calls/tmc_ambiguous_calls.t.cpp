// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cstdint>
#include <iostream>
#include <tmc_ambiguous_calls.h>
#include <utility>
#include <vector>

namespace {
int testStatus = 0;
void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100)
      ++testStatus;
  }
}
} // namespace
#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using T = TmcAmbiguousCalls;
using Exp = T::exp;
using BExp = T::bexp;
using Tree = T::tree;
using Term = T::term;

static const int kDeep = 1000000;

static uint64_t inc(uint64_t n) { return n + 1; }

// A digest of an expression, read without recursion: the number of nodes and
// a position-weighted hash of the variables in pre-order, so a definition
// swapped with its body changes it.
static std::pair<uint64_t, uint64_t> digest(const Exp &e) {
  uint64_t count = 0, sum = 0;
  std::vector<const Exp *> stack{&e};
  while (!stack.empty()) {
    const Exp *cur = stack.back();
    stack.pop_back();
    ++count;
    if (auto *v = std::get_if<Exp::Var>(&cur->v())) {
      sum = sum * 31 + v->v_0;
    } else {
      auto &l = std::get<Exp::Let>(cur->v());
      sum = sum * 31 + l.b->first;
      stack.push_back(&l.b->second);
      stack.push_back(l.body.get());
    }
  }
  return {count, sum};
}

static std::pair<uint64_t, uint64_t> digest(const BExp &e) {
  uint64_t count = 0, sum = 0;
  std::vector<const BExp *> stack{&e};
  while (!stack.empty()) {
    const BExp *cur = stack.back();
    stack.pop_back();
    ++count;
    if (auto *v = std::get_if<BExp::BVar>(&cur->v())) {
      sum = sum * 31 + v->v_0;
    } else {
      auto &l = std::get<BExp::BLet>(cur->v());
      sum = sum * 31 + l.b->v_0;
      stack.push_back(&l.b->def);
      stack.push_back(l.body.get());
    }
  }
  return {count, sum};
}

// In-order labels of a tree, read without recursion.
static std::vector<uint64_t> inorder(const Tree &t) {
  std::vector<uint64_t> out;
  std::vector<const Tree *> stack;
  const Tree *cur = &t;
  while (true) {
    while (auto *n = std::get_if<Tree::Node>(&cur->v())) {
      stack.push_back(cur);
      cur = n->l.get();
    }
    if (stack.empty())
      break;
    auto &n = std::get<Tree::Node>(stack.back()->v());
    stack.pop_back();
    out.push_back(n.x);
    cur = n.r.get();
  }
  return out;
}

static uint64_t inorder_sum(const Tree &t) {
  uint64_t s = 0;
  for (uint64_t x : inorder(t))
    s += x;
  return s;
}

// Let (i, Var i) (...): deep in the body.
static Exp deep_exp_body(int n) {
  Exp e = Exp::var(0);
  for (int i = 1; i <= n; ++i)
    e = Exp::let(std::make_pair(uint64_t(i), Exp::var(i)), std::move(e));
  return e;
}

// Let (i, ...) (Var i): deep in the definition, inside the pair.
static Exp deep_exp_def(int n) {
  Exp e = Exp::var(0);
  for (int i = 1; i <= n; ++i)
    e = Exp::let(std::make_pair(uint64_t(i), std::move(e)), Exp::var(i));
  return e;
}

static BExp deep_bexp_body(int n) {
  BExp e = BExp::bvar(0);
  for (int i = 1; i <= n; ++i)
    e = BExp::blet(T::binding<BExp>::bind(i, BExp::bvar(i)), std::move(e));
  return e;
}

static BExp deep_bexp_def(int n) {
  BExp e = BExp::bvar(0);
  for (int i = 1; i <= n; ++i)
    e = BExp::blet(T::binding<BExp>::bind(i, std::move(e)), BExp::bvar(i));
  return e;
}

// Node (...) i Leaf, a left spine; Node Leaf i (...), a right spine.
static Tree left_spine(int n) {
  Tree t = Tree::leaf();
  for (int i = 1; i <= n; ++i)
    t = Tree::node(std::move(t), i, Tree::leaf());
  return t;
}

static Tree right_spine(int n) {
  Tree t = Tree::leaf();
  for (int i = n; i >= 1; --i)
    t = Tree::node(Tree::leaf(), i, std::move(t));
  return t;
}

// The shape of a term: its number of nodes and of negations.
static std::pair<uint64_t, uint64_t> shape(const Term &t) {
  uint64_t count = 0, negs = 0;
  std::vector<const Term *> stack{&t};
  while (!stack.empty()) {
    const Term *cur = stack.back();
    stack.pop_back();
    ++count;
    if (auto *n = std::get_if<Term::Neg>(&cur->v())) {
      ++negs;
      stack.push_back(n->t.get());
    } else if (auto *a = std::get_if<Term::Add>(&cur->v())) {
      stack.push_back(a->a.get());
      stack.push_back(a->b.get());
    }
  }
  return {count, negs};
}

int main() {
  // The manual's example: Let (1, Let (2, Var 3) (Var 4)) (Var 5).
  {
    Exp e = Exp::let(
        std::make_pair(uint64_t(1),
                       Exp::let(std::make_pair(uint64_t(2), Exp::var(3)),
                                Exp::var(4))),
        Exp::var(5));
    Exp want = Exp::let(
        std::make_pair(uint64_t(2),
                       Exp::let(std::make_pair(uint64_t(3), Exp::var(4)),
                                Exp::var(5))),
        Exp::var(6));
    Exp m = e.map_vars(inc);
    ASSERT(digest(m) == digest(want));
    ASSERT(digest(m).first == 5);
  }
  {
    BExp e = BExp::blet(
        T::binding<BExp>::bind(
            1, BExp::blet(T::binding<BExp>::bind(2, BExp::bvar(3)),
                          BExp::bvar(4))),
        BExp::bvar(5));
    BExp want = BExp::blet(
        T::binding<BExp>::bind(
            2, BExp::blet(T::binding<BExp>::bind(3, BExp::bvar(4)),
                          BExp::bvar(5))),
        BExp::bvar(6));
    ASSERT(digest(e.map_bvars(inc)) == digest(want));
  }
  // Two calls in Node: the shape and the order of the labels are kept.
  {
    Tree t = Tree::node(
        Tree::node(Tree::leaf(), 1, Tree::node(Tree::leaf(), 2, Tree::leaf())),
        3, Tree::node(Tree::leaf(), 4, Tree::leaf()));
    ASSERT((inorder(t.map_tree(inc)) == std::vector<uint64_t>{2, 3, 4, 5}));
  }
  // One branch tail modulo cons alone, one with two calls.
  {
    Term t = Term::add(Term::neg(Term::lit(2)),
                       Term::add(Term::lit(3), Term::neg(Term::lit(4))));
    Term s = t.scale(10);
    ASSERT(s.eval() == 90);
    ASSERT(shape(s) == shape(t));
  }

  // Deep inputs: each recursive position in turn, a million deep.
  {
    Exp m = deep_exp_body(kDeep).map_vars(inc);
    ASSERT(digest(m).first == uint64_t(2 * kDeep + 1));
    // The innermost body is Var 0, mapped to Var 1.
    const Exp *cur = &m;
    while (auto *l = std::get_if<Exp::Let>(&cur->v()))
      cur = l->body.get();
    ASSERT(std::get<Exp::Var>(cur->v()).v_0 == 1);
  }
  {
    Exp m = deep_exp_def(kDeep).map_vars(inc);
    ASSERT(digest(m).first == uint64_t(2 * kDeep + 1));
    const Exp *cur = &m;
    while (auto *l = std::get_if<Exp::Let>(&cur->v()))
      cur = &l->b->second;
    ASSERT(std::get<Exp::Var>(cur->v()).v_0 == 1);
  }
  {
    BExp m = deep_bexp_body(kDeep).map_bvars(inc);
    ASSERT(digest(m).first == uint64_t(2 * kDeep + 1));
    BExp m2 = deep_bexp_def(kDeep).map_bvars(inc);
    ASSERT(digest(m2).first == uint64_t(2 * kDeep + 1));
  }
  {
    uint64_t n = kDeep;
    uint64_t want = n * (n + 1) / 2 + n;
    ASSERT(inorder_sum(left_spine(kDeep).map_tree(inc)) == want);
    ASSERT(inorder_sum(right_spine(kDeep).map_tree(inc)) == want);
  }
  {
    Term neg = Term::lit(1);
    for (int i = 0; i < kDeep; ++i)
      neg = Term::neg(std::move(neg));
    Term sn = neg.scale(3);
    ASSERT(sn.eval() == 3);
    ASSERT(shape(sn).second == uint64_t(kDeep));
    Term add = Term::lit(1);
    for (int i = 0; i < kDeep; ++i)
      add = Term::add(std::move(add), Term::lit(1));
    Term s = add.scale(2);
    ASSERT(s.eval() == uint64_t(2 * (kDeep + 1)));
    ASSERT(shape(s).first == uint64_t(2 * kDeep + 1));
  }

  if (testStatus == 0)
    std::cout << "All tmc_ambiguous_calls tests passed!" << std::endl;
  return testStatus;
}
