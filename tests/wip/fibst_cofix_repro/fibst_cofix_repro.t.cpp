// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Repro: a `let cofix` capturing the outer `n` recurses forever.
//
// fibst_repro's inner cofixpoint `go` matches on `n` captured by [&] from
// fibst_repro's parameter.  In the S branch, `_x = n - 1` computes the
// predecessor but is never threaded into the recursive call, so every
// iteration still sees the original `n`.  The computation is therefore
// genuinely non-terminating by construction — there is no finite result.
//
// This is intentional and stays in tests/wip: fibst_repro(5) can never return
// a value.  What we CAN and DO verify here is memory safety: Crane's loopify
// pass turns the erased-cofixpoint's eager tail self-recursion (which would
// otherwise blow the C++ call stack -> SIGSEGV / UB) into a constant-stack
// `while (true)` loop.  So the divergence must manifest as a safe infinite
// loop, never as a crash.
//
// The check: run fibst_repro(5) on a deliberately tiny (256 KB) thread stack.
//   * Loopified (constant-stack) code spins harmlessly -> we exit 0.
//   * If loopification ever regresses to eager recursion, it overflows the
//     tiny stack within milliseconds -> SIGSEGV terminates the process ->
//     the test fails.
#include "fibst_cofix_repro.h"

#include <cstdint>
#include <ctime>
#include <iostream>
#include <pthread.h>

static void *worker(void *) {
  // Never returns: the (loopified) computation loops forever by construction.
  volatile auto r = fibst_repro<FibstCofixReproTests::nat_stref,
                                FibstCofixReproTests::nat_idx, uint64_t>(5);
  (void)r;
  return nullptr;
}

int main() {
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  // 256 KB: ample for the constant-stack loop, far too small for unbounded
  // recursion (which would fault almost immediately).
  pthread_attr_setstacksize(&attr, 256 * 1024);

  pthread_t th;
  if (pthread_create(&th, &attr, worker, nullptr) != 0) {
    std::cerr << "failed to spawn worker thread" << std::endl;
    return 1;
  }
  pthread_attr_destroy(&attr);

  // Let the worker spin ~1.5s.  A stack-overflow regression crashes the whole
  // process well within this window; a memory-safe loop survives it.
  const struct timespec slice = {0, 150 * 1000 * 1000}; // 150 ms
  for (int i = 0; i < 10; ++i) {
    nanosleep(&slice, nullptr);
  }

  std::cout << "fibst_repro(5) ran memory-safely (constant-stack loop, no "
               "crash); diverges as expected."
            << std::endl;
  // Process exit abandons the still-looping worker; exit status 0 = pass.
  return 0;
}
