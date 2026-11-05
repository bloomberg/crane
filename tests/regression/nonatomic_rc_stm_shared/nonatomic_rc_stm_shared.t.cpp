// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <nonatomic_rc_stm_shared.h>
#include <shared_block.h>
#include <cassert>
#include <thread>
#include <vector>

// The unit asked for NonAtomicRc but uses STM: its counts stay atomic.  (A
// unit granted NonAtomicRc defines CRANE_NON_ATOMIC_RC before its runtime
// includes, which shared_block.h reports here.)
static_assert(crane::rc_is_atomic);

int main() {
  constexpr int threads = 8;
  constexpr int pushes = 500;
  auto box = NonatomicRcStmShared::make();
  std::vector<std::thread> workers;
  for (int t = 0; t < threads; ++t) {
    // Every push reads the variable, copying the list's head while other
    // threads replace it.  The list is walked (non-tail-recursively) only on
    // the main thread, after the joins: a worker's stack is 512 KB, too small
    // for thousands of frames under AddressSanitizer.
    workers.emplace_back([box, t] {
      for (int i = 0; i < pushes; ++i) {
        NonatomicRcStmShared::push(box, t * pushes + i);
      }
    });
  }
  for (auto &w : workers) {
    w.join();
  }
  assert(NonatomicRcStmShared::size(box) == threads * pushes);
  return 0;
}
