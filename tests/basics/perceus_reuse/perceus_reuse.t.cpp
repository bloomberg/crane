// Perceus reuse smoke test + allocation observable.
#include <cstdlib>
#include <cstdio>
#include <new>
#include "perceus_reuse.h"

static long g_allocs = 0;
void* operator new(std::size_t n) { ++g_allocs; void* p = std::malloc(n ? n : 1); if(!p) throw std::bad_alloc(); return p; }
void operator delete(void* p) noexcept { std::free(p); }
void operator delete(void* p, std::size_t) noexcept { std::free(p); }

static int testStatus = 0;
static void aSsErT(bool b, const char* s, int line) {
  if (b) { std::printf("Error %s(%d): %s\n", __FILE__, line, s); if (testStatus < 100) ++testStatus; }
}
#define ASSERT(X) aSsErT(!(X), #X, __LINE__)

// ---------------------------------------------------------------------------
// Runtime-header half of the feature: crane::take_for_reuse /
// crane::make_rc_reusing_unchecked, exercised in exactly the loop shape the
// loopify emitter produces for a TRMC map.  Hand-written (not generated) so the
// helpers are covered independently of the emitter that will call them.
// ---------------------------------------------------------------------------
namespace helpers_test {

struct Node {
  struct Nil {};
  struct Cons { long a0; crane::rc<Node> a1; };
  std::variant<Nil, Cons> v_;
  const std::variant<Nil, Cons>& v()     const { return v_; }
  std::variant<Nil, Cons>&       v_mut()       { return v_; }
};

static Node mk(long n) {                 // [1..n] with a by-value root cell
  crane::rc<Node> tail = crane::make_rc<Node>(Node{Node::Nil{}});
  for (long i = n; i >= 2; --i)
    tail = crane::make_rc<Node>(Node{Node::Cons{i, std::move(tail)}});
  return Node{Node::Cons{1, std::move(tail)}};
}

// map (+1) as an owning-cursor TRMC loop: _own/_uniq carry the recycling
// token; take_for_reuse latches _uniq off the first time a cell is shared.
static crane::rc<Node> map_inc(Node l) {
  crane::rc<Node>  _head{};
  crane::rc<Node>* _write = &_head;
  crane::rc<Node>  _own{};
  bool             _uniq  = true;
  Node*            _loop_l = &l;
  while (true) {
    if (std::holds_alternative<Node::Nil>(_loop_l->v())) {
      *_write = crane::make_rc<Node>(Node{Node::Nil{}});
      break;
    }
    auto _t = crane::take_for_reuse<Node::Cons>(*_loop_l, _own, _uniq);
    *_write = crane::make_rc_reusing_unchecked<Node>(
        std::move(_t.token), Node{Node::Cons{_t.fields.a0 + 1, crane::rc<Node>()}});
    _write  = &std::get<Node::Cons>((*_write)->v_mut()).a1;
    _own    = std::move(_t.fields.a1);
    _loop_l = _own.get();
  }
  return _head;
}

static bool spine_is(const Node& n, long len, long base) {
  const Node* p = &n;
  for (long i = 0; i < len; ++i) {
    auto* c = std::get_if<Node::Cons>(&p->v());
    if (!c || c->a0 != base + i) return false;
    p = c->a1.get();
  }
  return std::holds_alternative<Node::Nil>(p->v());
}

}  // namespace helpers_test

static R::lst build(int n) {   // Cons(n-1, ... Cons(0, Nil))
  R::lst l = R::lst::nil();
  for (int i = 0; i < n; ++i) l = R::lst::cons((std::uint64_t)i, std::move(l));
  return l;
}

int main() {
  const int N = 20000;
  // correctness: sum of map(+1) over 0..N-1 built list
  {
    R::lst l = build(N);
    long a0 = g_allocs;
    R::lst m = R::map1([](std::uint64_t x){ return x + 1; }, std::move(l));
    long during = g_allocs - a0;
    std::uint64_t s = R::sum1(m);
    std::uint64_t expect = 0; for (int i = 0; i < N; ++i) expect += (std::uint64_t)i + 1;
    std::printf("map1 sum=%llu expect=%llu ; allocations during map=%ld (N=%d)\n",
                (unsigned long long)s, (unsigned long long)expect, during, N);
    ASSERT(s == expect);
    // With reuse firing on the uniquely-owned input, map should allocate ~0 cells.
    ASSERT(during < N / 10);   // fires => far below N
  }
  // rev correctness
  {
    R::lst l = build(5);           // Cons4..Cons0
    R::lst r = R::rev1(std::move(l));
    // rev => Cons0..Cons4 ; sum unchanged
    ASSERT(R::sum1(r) == (std::uint64_t)(0+1+2+3+4));
  }
  // runtime helpers: unique spine recycles, shared spine copies and is intact
  {
    using namespace helpers_test;
    const long M = 1000;

    Node src = mk(M);
    long a0 = g_allocs;
    crane::rc<Node> out = map_inc(std::move(src));
    long during = g_allocs - a0;
    std::printf("take_for_reuse unique spine: %ld allocations for M=%ld\n", during, M);
    ASSERT(spine_is(*out, M, 2));
    ASSERT(during <= 3);          // only _head's first cell + the Nil terminator

    Node shared = mk(M);
    crane::rc<Node> pin = std::get<Node::Cons>(shared.v()).a1;   // alias the tail
    a0 = g_allocs;
    crane::rc<Node> out2 = map_inc(shared);
    long during2 = g_allocs - a0;
    std::printf("take_for_reuse shared spine: %ld allocations for M=%ld\n", during2, M);
    ASSERT(spine_is(shared, M, 1));   // original must be bit-for-bit intact
    ASSERT(spine_is(*out2, M, 2));
    ASSERT(during2 >= M);             // shared path allocates fresh cells
  }
  if (testStatus) std::printf("FAIL (%d)\n", testStatus); else std::printf("PASS\n");
  return testStatus;
}
