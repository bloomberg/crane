// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <hash.h>

#include <atomic>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <optional>
#include <memory>
#include <random>
#include <string>
#include <thread>
#include <utility>
#include <variant>
#include <vector>
#include <barrier>

// ============================================================================
//                     STANDARD BDE ASSERT TEST FUNCTION
// ----------------------------------------------------------------------------

// CHT is a template struct, so we access static members via CHT<K,V>::
template<typename K, typename V>
using CHT_funcs = CHT<K, V>;

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line)
{
    if (condition) {
        std::cout << "Error " __FILE__ "(" << line << "): " << message
             << "    (failed)" << std::endl;

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
  // Using std::hash<int> to distribute keys; return fits into int.
  return static_cast<int>(std::hash<int>{}(x));
}

// ---- Test 1: No lost updates under heavy contention via hash_update ----
// Many threads randomly pick keys and do: value := (prev.value_or(0) + 1).
// In parallel, we track the exact intended count per key in atomic counters.
// After joining, the table's values must match those counters exactly.
void test_no_lost_updates() {
  std::cout << "[Test 1] No lost updates via hash_update...\n";

  const int NUM_KEYS = 2000;
  const int NUM_THREADS = 8;
  const int OPS_PER_THREAD = 100'000; // total increments (fast but stressful) ~= 8e5 (fast but stressful)
  const int REQUESTED_BUCKETS = 4096;

  auto tbl = CHT<int, int>::new_hash<int, int>(int_eq, int_hash, REQUESTED_BUCKETS);
  std::vector<std::atomic<int>> expected(NUM_KEYS);
  for (auto &a : expected) a.store(0, std::memory_order_relaxed);

  // Start together for maximum overlap.
  std::barrier start_barrier(NUM_THREADS);

  auto worker = [&](int tid) {
    std::mt19937_64 rng(std::random_device{}() ^ (uint64_t(tid) << 32));
    std::uniform_int_distribution<int> key_dist(0, NUM_KEYS - 1);

    start_barrier.arrive_and_wait();

    for (int i = 0; i < OPS_PER_THREAD; ++i) {
      int k = key_dist(rng);

      // Increment in the table (monotonic, so we can assert exact totals).
      (void)tbl->hash_update(k, [](std::optional<int> prev) {
        return prev.value_or(0) + 1;
      });

      // Ground truth in atomics (no locking, linearizable counter).
      expected[k].fetch_add(1, std::memory_order_relaxed);
    }
  };

  std::vector<std::thread> threads;
  threads.reserve(NUM_THREADS);
  for (int t = 0; t < NUM_THREADS; ++t) threads.emplace_back(worker, t);
  for (auto &th : threads) th.join();

  // Verify exact equality per key.
  for (int k = 0; k < NUM_KEYS; ++k) {
    const int want = expected[k].load(std::memory_order_relaxed);
    auto got = tbl->get(k);
    if (want == 0) {
      // Key may never have been touched; should be absent.
      assert(!got.has_value());
    } else {
      assert(got.has_value());
      assert(*got == want);
    }
  }

  std::cout << "  ✓ Passed: all keys match expected counters.\n";
}

// ---- Test 2: Delete has a single winner per key ----
// Pre-insert keys with known values, then let many threads race to delete.
// Exactly one delete should succeed per key (optional engaged), and in the end
// all keys must be absent.
void test_delete_single_winner() {
  std::cout << "[Test 2] Deletes: single winner per key under contention...\n";

  const int NUM_KEYS = 5'000;
  const int NUM_THREADS = 6;
  const int REQUESTED_BUCKETS = 8192;

  auto tbl = CHT<int, int>::new_hash<int, int>(int_eq, int_hash, REQUESTED_BUCKETS);

  // Pre-insert unique keys -> value = 10 * key (easy to check).
  for (int k = 0; k < NUM_KEYS; ++k) {
    tbl->put(k, 10 * k);
  }

  std::atomic<int> successes{0};
  std::barrier start_barrier(NUM_THREADS);

  auto worker = [&](int tid) {
    (void)tid;
    start_barrier.arrive_and_wait();

    // Each thread attempts to delete every key once.
    // Only one thread should get a non-empty optional per key.
    for (int k = 0; k < NUM_KEYS; ++k) {
      auto res = tbl->hash_delete(k);
      if (res.has_value()) {
        // If you won, the value must be exactly what we inserted.
        assert(*res == 10 * k);
        successes.fetch_add(1, std::memory_order_relaxed);
      }
    }
  };

  std::vector<std::thread> threads;
  threads.reserve(NUM_THREADS);
  for (int t = 0; t < NUM_THREADS; ++t) threads.emplace_back(worker, t);
  for (auto &th : threads) th.join();

  // Exactly NUM_KEYS deletes must have succeeded overall.
  assert(successes.load(std::memory_order_relaxed) == NUM_KEYS);

  // Now the table must be empty with respect to these keys.
  for (int k = 0; k < NUM_KEYS; ++k) {
    auto g = tbl->get(k);
    assert(!g.has_value());
    int dflt = -1;
    int v = tbl->get_or(k, dflt);
    assert(v == dflt);
  }

  std::cout << "  ✓ Passed: exactly one successful delete per key; keys absent afterwards.\n";
}

// ---- Test 3: Racy puts/gets smoke test ----
// Threads randomly interleave gets and puts across a shared keyset to stress
// the STM. We only assert basic sanity (no crashes, returned values are within
// known bounds). Run under TSAN to surface races in implementation if any.
void test_racy_puts_gets_smoke() {
  std::cout << "[Test 3] Racy puts/gets smoke test...\n";

  const int NUM_KEYS = 1000;
  const int NUM_THREADS = 8;
  const int OPS_PER_THREAD = 50'000;
  const int REQUESTED_BUCKETS = 2048;

  auto tbl = CHT<int, int>::new_hash<int, int>(int_eq, int_hash, REQUESTED_BUCKETS);

  // Seed some values so gets often find something.
  for (int k = 0; k < NUM_KEYS; ++k) {
    tbl->put(k, 0);
  }

  std::barrier start_barrier(NUM_THREADS);

  auto worker = [&](int tid) {
    std::mt19937 rng(std::random_device{}() ^ (tid * 0x9E3779B9));
    std::uniform_int_distribution<int> key_dist(0, NUM_KEYS - 1);
    std::uniform_int_distribution<int> op_dist(0, 99); // 0..39 put, 40..99 get (60% gets)

    start_barrier.arrive_and_wait();

    for (int i = 0; i < OPS_PER_THREAD; ++i) {
      int k = key_dist(rng);
      int op = op_dist(rng);

      if (op < 40) {
        // Concurrent writers keep overwriting; final value should be any thread id.
        tbl->put(k, tid);
      } else {
        // Concurrent readers just fetch; value (if present) must be a plausible tid.
        auto v = tbl->get(k);
        if (v.has_value()) {
          int x = *v;
          assert(x >= 0 && x < NUM_THREADS);
        }
      }
    }
  };

  std::vector<std::thread> threads;
  threads.reserve(NUM_THREADS);
  for (int t = 0; t < NUM_THREADS; ++t) threads.emplace_back(worker, t);
  for (auto &th : threads) th.join();

  // Basic post-condition sanity: keys should still be present with a valid tid.
  for (int k = 0; k < NUM_KEYS; ++k) {
    auto v = tbl->get(k);
    if (v.has_value()) {
      int x = *v;
      assert(x >= 0 && x < NUM_THREADS);
    }
  }

  std::cout << "  ✓ Passed: smoke test completed without violations.\n";
}

int main() {
  try {
    test_no_lost_updates();
    test_delete_single_winner();
    test_racy_puts_gets_smoke();
  } catch (const std::exception &e) {
    std::cerr << "Test failed with exception: " << e.what() << "\n";
    return 1;
  } catch (...) {
    std::cerr << "Test failed with unknown exception.\n";
    return 1;
  }

  std::cout << "\nAll tests passed ✅\n";
  std::cout << "Tip: also run under ThreadSanitizer (-fsanitize=thread) for extra confidence.\n";
  return 0;
}

// clang++ -I. -std=c++23 -fsanitize=thread -O2 hash.o hash.t.cpp -o hash.t.exe; ./hash.t.exe
// clang++ -I. -std=c++23 -c hash.cpp -o hash.o
