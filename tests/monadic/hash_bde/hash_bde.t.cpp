// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <hash_bde.h>

#include <bsl_atomic.h>
#include <bsls_assert.h>

#include <bsl_cstdint.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_optional.h>
#include <bsl_memory.h>
#include <bsl_random.h>
#include <bsl_string.h>
#include <bsl_thread.h>
#include <bsl_utility.h>
#include <bsl_variant.h>
#include <bsl_vector.h>

// bsl::barrier doesn't have a 1:1 BDE wrapper.
// Use bsl::barrier from:
#include <bsl_barrier.h>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

using namespace CHT;

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        bsl::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << bsl::endl;

        if (0 <= testStatus && testStatus <= 100) {
            ++testStatus;
        }
    }
}

}  // close unnamed namespace

#define ASSERT(X)                                              \
    aSsErT(!(X), #X, __LINE__);


// ---- Helpers: eq and hash for int keys ----
static inline bool int_eq(int a, int b) { return a == b; }
static inline int int_hash(int x) {
  // Using bsl::hash<int> to distribute keys; return fits into int.
  return static_cast<int>(bsl::hash<int>{}(x));
}

// ---- Test 1: No lost updates under heavy contention via hash_update ----
// Many threads randomly pick keys and do: value := (prev.value_or(0) + 1).
// In parallel, we track the exact intended count per key in atomic counters.
// After joining, the table's values must match those counters exactly.
void test_no_lost_updates() {
  bsl::cout << "[Test 1] No lost updates via hash_update...\n";

  const int NUM_KEYS = 2000;
  const int NUM_THREADS = 8;
  const int OPS_PER_THREAD = 100'000; // total increments (fast but stressful) ~= 8e5 (fast but stressful)
  const int REQUESTED_BUCKETS = 4096;

  auto tbl = new_hash<int, int>(int_eq, int_hash, REQUESTED_BUCKETS);
  bsl::vector<bsl::atomic<int>> expected(NUM_KEYS);
  for (auto &a : expected) a.store(0, bsl::memory_order_relaxed);

  // Start together for maximum overlap.
  bsl::barrier start_barrier(NUM_THREADS);

  auto worker = [&](int tid) {
    bsl::mt19937_64 rng(bsl::random_device{}() ^ (uint64_t(tid) << 32));
    bsl::uniform_int_distribution<int> key_dist(0, NUM_KEYS - 1);

    start_barrier.arrive_and_wait();

    for (int i = 0; i < OPS_PER_THREAD; ++i) {
      int k = key_dist(rng);

      // Increment in the table (monotonic, so we can assert exact totals).
      (void)hash_update<int, int>(tbl, k, [](bsl::optional<int> prev) {
        return prev.value_or(0) + 1;
      });

      // Ground truth in atomics (no locking, linearizable counter).
      expected[k].fetch_add(1, bsl::memory_order_relaxed);
    }
  };

  bsl::vector<bsl::thread> threads;
  threads.reserve(NUM_THREADS);
  for (int t = 0; t < NUM_THREADS; ++t) threads.emplace_back(worker, t);
  for (auto &th : threads) th.join();

  // Verify exact equality per key.
  for (int k = 0; k < NUM_KEYS; ++k) {
    const int want = expected[k].load(bsl::memory_order_relaxed);
    auto got = get<int, int>(tbl, k);
    if (want == 0) {
      // Key may never have been touched; should be absent.
      BSLS_ASSERT(!got.has_value());
    } else {
      BSLS_ASSERT(got.has_value());
      BSLS_ASSERT(*got == want);
    }
  }

  bsl::cout << "  ✓ Passed: all keys match expected counters.\n";
}

// ---- Test 2: Delete has a single winner per key ----
// Pre-insert keys with known values, then let many threads race to delete.
// Exactly one delete should succeed per key (optional engaged), and in the end
// all keys must be absent.
void test_delete_single_winner() {
  bsl::cout << "[Test 2] Deletes: single winner per key under contention...\n";

  const int NUM_KEYS = 5'000;
  const int NUM_THREADS = 6;
  const int REQUESTED_BUCKETS = 8192;

  auto tbl = new_hash<int, int>(int_eq, int_hash, REQUESTED_BUCKETS);

  // Pre-insert unique keys -> value = 10 * key (easy to check).
  for (int k = 0; k < NUM_KEYS; ++k) {
    put<int, int>(tbl, k, 10 * k);
  }

  bsl::atomic<int> successes{0};
  bsl::barrier start_barrier(NUM_THREADS);

  auto worker = [&](int tid) {
    (void)tid;
    start_barrier.arrive_and_wait();

    // Each thread attempts to delete every key once.
    // Only one thread should get a non-empty optional per key.
    for (int k = 0; k < NUM_KEYS; ++k) {
      auto res = hash_delete<int, int>(tbl, k);
      if (res.has_value()) {
        // If you won, the value must be exactly what we inserted.
        BSLS_ASSERT(*res == 10 * k);
        successes.fetch_add(1, bsl::memory_order_relaxed);
      }
    }
  };

  bsl::vector<bsl::thread> threads;
  threads.reserve(NUM_THREADS);
  for (int t = 0; t < NUM_THREADS; ++t) threads.emplace_back(worker, t);
  for (auto &th : threads) th.join();

  // Exactly NUM_KEYS deletes must have succeeded overall.
  BSLS_ASSERT(successes.load(bsl::memory_order_relaxed) == NUM_KEYS);

  // Now the table must be empty with respect to these keys.
  for (int k = 0; k < NUM_KEYS; ++k) {
    auto g = get<int, int>(tbl, k);
    BSLS_ASSERT(!g.has_value());
    int dflt = -1;
    int v = get_or<int, int>(tbl, k, dflt);
    BSLS_ASSERT(v == dflt);
  }

  bsl::cout << "  ✓ Passed: exactly one successful delete per key; keys absent afterwards.\n";
}

// ---- Test 3: Racy puts/gets smoke test ----
// Threads randomly interleave gets and puts across a shared keyset to stress
// the STM. We only assert basic sanity (no crashes, returned values are within
// known bounds). Run under TSAN to surface races in implementation if any.
void test_racy_puts_gets_smoke() {
  bsl::cout << "[Test 3] Racy puts/gets smoke test...\n";

  const int NUM_KEYS = 1000;
  const int NUM_THREADS = 8;
  const int OPS_PER_THREAD = 50'000;
  const int REQUESTED_BUCKETS = 2048;

  auto tbl = new_hash<int, int>(int_eq, int_hash, REQUESTED_BUCKETS);

  // Seed some values so gets often find something.
  for (int k = 0; k < NUM_KEYS; ++k) {
    put<int, int>(tbl, k, 0);
  }

  bsl::barrier start_barrier(NUM_THREADS);

  auto worker = [&](int tid) {
    bsl::mt19937 rng(bsl::random_device{}() ^ (tid * 0x9E3779B9));
    bsl::uniform_int_distribution<int> key_dist(0, NUM_KEYS - 1);
    bsl::uniform_int_distribution<int> op_dist(0, 99); // 0..39 put, 40..99 get (60% gets)

    start_barrier.arrive_and_wait();

    for (int i = 0; i < OPS_PER_THREAD; ++i) {
      int k = key_dist(rng);
      int op = op_dist(rng);

      if (op < 40) {
        // Concurrent writers keep overwriting; final value should be any thread id.
        put<int, int>(tbl, k, tid);
      } else {
        // Concurrent readers just fetch; value (if present) must be a plausible tid.
        auto v = get<int, int>(tbl, k);
        if (v.has_value()) {
          int x = *v;
          BSLS_ASSERT(x >= 0 && x < NUM_THREADS);
        }
      }
    }
  };

  bsl::vector<bsl::thread> threads;
  threads.reserve(NUM_THREADS);
  for (int t = 0; t < NUM_THREADS; ++t) threads.emplace_back(worker, t);
  for (auto &th : threads) th.join();

  // Basic post-condition sanity: keys should still be present with a valid tid.
  for (int k = 0; k < NUM_KEYS; ++k) {
    auto v = get<int, int>(tbl, k);
    if (v.has_value()) {
      int x = *v;
      BSLS_ASSERT(x >= 0 && x < NUM_THREADS);
    }
  }

  bsl::cout << "  ✓ Passed: smoke test completed without violations.\n";
}

int main() {
  try {
    test_no_lost_updates();
    test_delete_single_winner();
    test_racy_puts_gets_smoke();
  } catch (const bsl::exception &e) {
    bsl::cerr << "Test failed with exception: " << e.what() << "\n";
    return 1;
  } catch (...) {
    bsl::cerr << "Test failed with unknown exception.\n";
    return 1;
  }

  bsl::cout << "\nAll tests passed ✅\n";
  bsl::cout << "Tip: also run under ThreadSanitizer (-fsanitize=thread) for extra confidence.\n";
  return 0;
}

/*
  clang++ -c -std=c++20 -Wno-deprecated-literal-operator -Wno-unused-command-line-argument \
  -I. -I~/bde_install/include \
  hash_bde.cpp \
  -L~/bde_install/lib \
  -lbsl -lbal -lbdl -lbbl -lbbryu -linteldfp -lpcre2 \
  -o hash_bde.o

  clang++ -std=c++20 -fsanitize=thread -Wno-deprecated-literal-operator -Wno-unused-command-line-argument \
  -I. -I~/bde_install/include \
  hash_bde.o hash_bde.t.cpp \
  -L~/bde_install/lib \
  -lbsl -lbal -lbdl -lbbl -lbbryu -linteldfp -lpcre2 \
  -o hash_bde.t.exe
*/
