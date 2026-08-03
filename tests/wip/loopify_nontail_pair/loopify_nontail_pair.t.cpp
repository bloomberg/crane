// Loopification regression: a well-founded self-recursion whose recursive
// call's result is destructured by a single-branch (irrefutable) tuple `match`
// used directly as the branch's returned value — the shape of the extracted
// lexer `lex'_M`.
//
// Before the fix, loopify's `has_recursive_branch_dependency` guard treated the
// recursive call in that single-branch destructure's scrutinee position as a
// disqualifying "branch dependency" (the destructure lowers to a single-branch
// `Scustom_case`/`Smatch` whose scrutinee is the recursive call).  It left
// `countdown` as plain C++ recursion, so a deep call overflowed the stack.
// After the fix it is loopified into an explicit-stack loop using O(1) C++
// stack.
//
// We run on a deliberately small (512 KiB) thread stack with a large input
// list: un-loopified recursion 1,000,000 frames deep would overflow it, so
// completing successfully demonstrates the recursion no longer consumes C++
// stack per call.
#include "loopify_nontail_pair.h"

#include <cassert>
#include <iostream>
#include <pthread.h>

static const uint64_t N = 1000000;

static void *run(void *) {
  // Build a list [0, 1, ..., N-1] iteratively (cons is O(1); the List
  // destructor is iterative, so no teardown overflow either).
  List<uint64_t> l = List<uint64_t>::nil();
  for (uint64_t i = 0; i < N; ++i)
    l = List<uint64_t>::cons(N - 1 - i, std::move(l));
  auto c = LoopifyNontailPair::run_count(l);
  assert(c == N);
  return nullptr;
}

int main() {
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  // 512 KiB: far too small for 1,000,000 frames of genuine C++ recursion.
  pthread_attr_setstacksize(&attr, 512 * 1024);
  pthread_t t;
  int rc = pthread_create(&t, &attr, run, nullptr);
  assert(rc == 0);
  pthread_join(t, nullptr);
  pthread_attr_destroy(&attr);
  std::cout << "loopify_nontail_pair: run_count(list of " << N << ") == " << N
            << " on a 512 KiB stack PASSED" << std::endl;
  return 0;
}
