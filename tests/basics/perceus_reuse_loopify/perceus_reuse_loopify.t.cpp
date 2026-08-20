// Perceus reuse THROUGH loopify: the same linear map/rev as perceus_reuse, but
// with `Set Crane Loopify`, so the TMC while loop -- not translation's
// dual-path match -- is what recycles cells, via the owning cursor
// (_own/_uniq/crane::reuse_step).  The allocation counts are the observable:
// a uniquely-owned spine must map with ~no allocations, and a shared one must
// allocate a fresh spine and leave the original intact.
#include <cstdlib>
#include <cstdio>
#include <new>
#include "perceus_reuse_loopify.h"

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
  std::uint64_t expect = 0; for (int i = 0; i < N; ++i) expect += (std::uint64_t)i + 1;

  // uniquely-owned spine: the cursor recycles every cell
  {
    R::lst l = build(N);
    long a0 = g_allocs;
    R::lst m = R::map1([](std::uint64_t x){ return x + 1; }, std::move(l));
    long during = g_allocs - a0;
    std::printf("loopify map1 (unique): allocations=%ld (N=%d)\n", during, N);
    ASSERT(R::sum1(m) == expect);
    ASSERT(during < N / 10);
  }

  // shared spine: the cursor must fall back to allocating, and must not
  // disturb the list the other handle still sees
  {
    R::lst l = build(N);
    R::lst keep = l;                       // second handle on the whole spine
    long a0 = g_allocs;
    R::lst m = R::map1([](std::uint64_t x){ return x + 1; }, l);
    long during = g_allocs - a0;
    std::printf("loopify map1 (shared): allocations=%ld (N=%d)\n", during, N);
    ASSERT(R::sum1(m) == expect);
    ASSERT(R::sum1(keep) == expect - (std::uint64_t)N);   // original untouched
    ASSERT(R::sum1(l) == expect - (std::uint64_t)N);
    ASSERT(during >= N / 2);               // fresh cells, not recycled ones
  }

  // rev (plain tail recursion, no TMC cells) still correct under both flags
  {
    R::lst l = build(5);
    R::lst r = R::rev1(std::move(l));
    ASSERT(R::sum1(r) == (std::uint64_t)(0+1+2+3+4));
  }

  if (testStatus) std::printf("FAIL (%d)\n", testStatus); else std::printf("PASS\n");
  return testStatus;
}
