// A loopified list builder assembles its result in place: n elements cost n
// allocations -- n-1 cells below the root and the terminal Nil -- and an empty
// result none.  A shared tail it appends onto stays intact.
#include "tmc_value_root.h"

#include <cassert>
#include <cstdlib>
#include <new>

static long g_allocs = 0;
void *operator new(std::size_t n) {
  ++g_allocs;
  if (void *p = std::malloc(n ? n : 1)) return p;
  throw std::bad_alloc();
}
void operator delete(void *p) noexcept { std::free(p); }
void operator delete(void *p, std::size_t) noexcept { std::free(p); }

using L = TmcValueRoot::lst;

static long allocations(auto &&f) {
  long before = g_allocs;
  f();
  return g_allocs - before;
}

static int len(const L &l) {
  int n = 0;
  for (const L *p = &l; std::holds_alternative<L::Cons>(p->v());
       p = std::get<L::Cons>(p->v()).l.get())
    ++n;
  return n;
}

int main() {
  assert(allocations([] { L r = TmcValueRoot::range(0, 0); assert(len(r) == 0); }) == 0);
  assert(allocations([] { L r = TmcValueRoot::range(0, 1); assert(len(r) == 1); }) == 1);
  assert(allocations([] { L r = TmcValueRoot::range(0, 5); assert(len(r) == 5); }) == 5);

  L xs = TmcValueRoot::range(0, 3);
  L ys = TmcValueRoot::range(10, 2);
  L zs = TmcValueRoot::app(xs, ys);
  assert(len(zs) == 5 && len(ys) == 2 && len(xs) == 3);

  L s = TmcValueRoot::stutter(xs);
  assert(len(s) == 6);
  return 0;
}
