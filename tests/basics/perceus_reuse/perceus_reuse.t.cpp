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
  if (testStatus) std::printf("FAIL (%d)\n", testStatus); else std::printf("PASS\n");
  return testStatus;
}
