// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <functional>
#include <iomanip>
#include <iostream>
#include <memory>
#include <mini_stm.h>
#include <optional>
#include <random>
#include <skiplist.h>
#include <skipnode.h>
#include <string>
#include <thread>
#include <utility>
#include <variant>
#include <vector>

// Initialize random seed
struct RandomInit {
    RandomInit() { std::srand(42); }  // Fixed seed for reproducibility
} random_init;

// Helper for comparison functions
static bool nat_lt(unsigned int a, unsigned int b) { return a < b; }
static bool nat_eq(unsigned int a, unsigned int b) { return a == b; }

// =============================================================================
//                         CONCURRENT TESTS
// =============================================================================

// Test: Multiple threads inserting concurrently
bool test_concurrent_insert() {
    const int NUM_THREADS = 4;
    const int ITEMS_PER_THREAD = 100;

    auto sl = stm::atomically([] {
        return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
    });

    std::vector<std::thread> threads;
    std::atomic<bool> failed{false};

    for (int t = 0; t < NUM_THREADS; t++) {
        threads.emplace_back([&sl, t, &failed]() {
            for (int i = 0; i < ITEMS_PER_THREAD; i++) {
                unsigned int key = t * ITEMS_PER_THREAD + i;
                unsigned int value = key * 10;
                try {
                    stm::atomically([&] {
                        sl->insert(nat_lt, nat_eq, key, value, std::rand() % 16);
                    });
                } catch (...) {
                    failed = true;
                }
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    if (failed) {
        std::cerr << "Exception during concurrent insert" << std::endl;
        return false;
    }

    // Verify all items were inserted
    unsigned int len = stm::atomically([&] { return sl->length(); });
    if (len != NUM_THREADS * ITEMS_PER_THREAD) {
        std::cerr << "Expected " << NUM_THREADS * ITEMS_PER_THREAD
                  << " items, got " << len << std::endl;
        return false;
    }

    // Verify all items can be found
    for (int t = 0; t < NUM_THREADS; t++) {
        for (int i = 0; i < ITEMS_PER_THREAD; i++) {
            unsigned int key = t * ITEMS_PER_THREAD + i;
            auto result = stm::atomically([&] {
                return sl->lookup(nat_lt, nat_eq, key);
            });
            if (!result.has_value() || *result != key * 10) {
                std::cerr << "Failed to find key " << key << std::endl;
                return false;
            }
        }
    }

    return true;
}

// Test: Multiple threads reading while others insert
bool test_concurrent_read_write() {
    const int NUM_WRITERS = 2;
    const int NUM_READERS = 2;
    const int ITEMS_PER_WRITER = 100;
    const int READS_PER_READER = 500;

    auto sl = stm::atomically([] {
        return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
    });

    // Pre-populate with some items
    stm::atomically([&] {
        for (unsigned int i = 0; i < 50; i++) {
            sl->insert(nat_lt, nat_eq, i, i * 10, std::rand() % 16);
        }
    });

    std::atomic<bool> failed{false};
    std::atomic<int> successful_reads{0};
    std::vector<std::thread> threads;

    // Writer threads
    for (int w = 0; w < NUM_WRITERS; w++) {
        threads.emplace_back([&sl, w, &failed]() {
            for (int i = 0; i < ITEMS_PER_WRITER; i++) {
                unsigned int key = 1000 + w * ITEMS_PER_WRITER + i;
                try {
                    stm::atomically([&] {
                        sl->insert(nat_lt, nat_eq, key, key * 10, std::rand() % 16);
                    });
                } catch (...) {
                    failed = true;
                }
            }
        });
    }

    // Reader threads
    for (int r = 0; r < NUM_READERS; r++) {
        threads.emplace_back([&sl, &failed, &successful_reads]() {
            for (int i = 0; i < READS_PER_READER; i++) {
                unsigned int key = std::rand() % 50;  // Read from pre-populated range
                try {
                    auto result = stm::atomically([&] {
                        return sl->lookup(nat_lt, nat_eq, key);
                    });
                    if (result.has_value()) {
                        successful_reads++;
                    }
                } catch (...) {
                    failed = true;
                }
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    if (failed) {
        std::cerr << "Exception during concurrent read/write" << std::endl;
        return false;
    }

    // Verify final length
    unsigned int len = stm::atomically([&] { return sl->length(); });
    unsigned int expected = 50 + NUM_WRITERS * ITEMS_PER_WRITER;
    if (len != expected) {
        std::cerr << "Expected " << expected << " items, got " << len << std::endl;
        return false;
    }

    return true;
}

// Test: Producer-consumer pattern
bool test_concurrent_producer_consumer() {
    const int NUM_ITEMS = 200;

    auto sl = stm::atomically([] {
        return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
    });

    std::atomic<bool> producer_done{false};
    std::atomic<int> consumed{0};
    std::atomic<bool> failed{false};

    // Producer thread
    std::thread producer([&]() {
        for (int i = 1; i <= NUM_ITEMS; i++) {
            try {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), std::rand() % 16);
                });
            } catch (...) {
                failed = true;
            }
            // Small delay to interleave with consumer
            if (i % 10 == 0) {
                std::this_thread::yield();
            }
        }
        producer_done = true;
    });

    // Consumer thread
    std::thread consumer([&]() {
        while (!producer_done || consumed < NUM_ITEMS) {
            try {
                auto result = stm::atomically([&]() -> std::optional<std::pair<unsigned int, unsigned int>> {
                    return sl->popFront();
                });
                if (result.has_value()) {
                    consumed++;
                } else {
                    std::this_thread::yield();
                }
            } catch (...) {
                failed = true;
            }
        }
    });

    producer.join();
    consumer.join();

    if (failed) {
        std::cerr << "Exception during producer-consumer test" << std::endl;
        return false;
    }

    // All items should be consumed
    if (consumed != NUM_ITEMS) {
        std::cerr << "Expected " << NUM_ITEMS << " consumed, got " << consumed << std::endl;
        return false;
    }

    // List should be empty
    bool isEmpty = stm::atomically([&] { return sl->isEmpty(); });
    if (!isEmpty) {
        std::cerr << "List should be empty after consuming all items" << std::endl;
        return false;
    }

    return true;
}

// Test: Multiple threads doing mixed operations
bool test_concurrent_mixed_operations() {
    const int NUM_THREADS = 4;
    const int OPS_PER_THREAD = 100;

    auto sl = stm::atomically([] {
        return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
    });

    // Pre-populate
    stm::atomically([&] {
        for (unsigned int i = 0; i < 100; i++) {
            sl->insert(nat_lt, nat_eq, i, i * 10, std::rand() % 16);
        }
    });

    std::atomic<bool> failed{false};
    std::vector<std::thread> threads;

    for (int t = 0; t < NUM_THREADS; t++) {
        threads.emplace_back([&sl, t, &failed]() {
            for (int i = 0; i < OPS_PER_THREAD; i++) {
                try {
                    int op = std::rand() % 4;
                    unsigned int key = std::rand() % 200;

                    switch (op) {
                        case 0:  // Insert
                            stm::atomically([&] {
                                sl->insert(nat_lt, nat_eq, key, key * 10, std::rand() % 16);
                            });
                            break;
                        case 1:  // Lookup
                            stm::atomically([&] {
                                sl->lookup(nat_lt, nat_eq, key);
                            });
                            break;
                        case 2:  // Member check
                            stm::atomically([&] {
                                sl->member(nat_lt, nat_eq, key);
                            });
                            break;
                        case 3:  // Remove
                            stm::atomically([&] {
                                sl->remove(nat_lt, nat_eq, key);
                            });
                            break;
                    }
                } catch (...) {
                    failed = true;
                }
            }
        });
    }

    for (auto& t : threads) {
        t.join();
    }

    if (failed) {
        std::cerr << "Exception during concurrent mixed operations" << std::endl;
        return false;
    }

    // Verify list is in consistent state
    unsigned int len = stm::atomically([&] { return sl->length(); });
    bool isEmpty = stm::atomically([&] { return sl->isEmpty(); });

    // Basic sanity checks
    if (len > 0 && isEmpty) {
        std::cerr << "Inconsistent state: length=" << len << " but isEmpty=true" << std::endl;
        return false;
    }
    if (len == 0 && !isEmpty) {
        std::cerr << "Inconsistent state: length=0 but isEmpty=false" << std::endl;
        return false;
    }

    return true;
}

int main(int argc, char* argv[]) {
    unsigned int passed = 0;
    unsigned int total = 17;  // 13 original + 4 concurrent tests

    // Original tests
    bool r1 = skiplist_test::test_insert_lookup();
    std::cout << "test_insert_lookup: " << (r1 ? "PASS" : "FAIL") << std::endl;
    if (r1) passed++;

    bool r2 = skiplist_test::test_delete();
    std::cout << "test_delete: " << (r2 ? "PASS" : "FAIL") << std::endl;
    if (r2) passed++;

    bool r3 = skiplist_test::test_update();
    std::cout << "test_update: " << (r3 ? "PASS" : "FAIL") << std::endl;
    if (r3) passed++;

    bool r4 = skiplist_test::test_minimum();
    std::cout << "test_minimum: " << (r4 ? "PASS" : "FAIL") << std::endl;
    if (r4) passed++;

    // BDE-compatible operation tests
    bool r5 = skiplist_test::test_length_isEmpty();
    std::cout << "test_length_isEmpty: " << (r5 ? "PASS" : "FAIL") << std::endl;
    if (r5) passed++;

    bool r6 = skiplist_test::test_front_back();
    std::cout << "test_front_back: " << (r6 ? "PASS" : "FAIL") << std::endl;
    if (r6) passed++;

    bool r7 = skiplist_test::test_popFront();
    std::cout << "test_popFront: " << (r7 ? "PASS" : "FAIL") << std::endl;
    if (r7) passed++;

    bool r8 = skiplist_test::test_addUnique();
    std::cout << "test_addUnique: " << (r8 ? "PASS" : "FAIL") << std::endl;
    if (r8) passed++;

    bool r9 = skiplist_test::test_find();
    std::cout << "test_find: " << (r9 ? "PASS" : "FAIL") << std::endl;
    if (r9) passed++;

    bool r10 = skiplist_test::test_navigation();
    std::cout << "test_navigation: " << (r10 ? "PASS" : "FAIL") << std::endl;
    if (r10) passed++;

    bool r11 = skiplist_test::test_bounds();
    std::cout << "test_bounds: " << (r11 ? "PASS" : "FAIL") << std::endl;
    if (r11) passed++;

    bool r12 = skiplist_test::test_removeAll();
    std::cout << "test_removeAll: " << (r12 ? "PASS" : "FAIL") << std::endl;
    if (r12) passed++;

    bool r13 = skiplist_test::test_bde_api();
    std::cout << "test_bde_api: " << (r13 ? "PASS" : "FAIL") << std::endl;
    if (r13) passed++;

    // Concurrent tests
    std::cout << "\n--- Concurrent Tests ---" << std::endl;

    bool r14 = test_concurrent_insert();
    std::cout << "test_concurrent_insert: " << (r14 ? "PASS" : "FAIL") << std::endl;
    if (r14) passed++;

    bool r15 = test_concurrent_read_write();
    std::cout << "test_concurrent_read_write: " << (r15 ? "PASS" : "FAIL") << std::endl;
    if (r15) passed++;

    bool r16 = test_concurrent_producer_consumer();
    std::cout << "test_concurrent_producer_consumer: " << (r16 ? "PASS" : "FAIL") << std::endl;
    if (r16) passed++;

    bool r17 = test_concurrent_mixed_operations();
    std::cout << "test_concurrent_mixed_operations: " << (r17 ? "PASS" : "FAIL") << std::endl;
    if (r17) passed++;

    std::cout << "\nSkipList tests passed: " << passed << "/" << total << std::endl;

    if (passed == total) {
        std::cout << "All tests passed!" << std::endl;
    } else {
        std::cout << "Some tests failed." << std::endl;
        return 1;
    }

    // Run benchmarks if --benchmark flag is passed
    bool run_bench = false;
    for (int i = 1; i < argc; i++) {
        if (std::strcmp(argv[i], "--benchmark") == 0 || std::strcmp(argv[i], "-b") == 0) {
            run_bench = true;
        }
    }

    if (run_bench) {
        std::cout << "\n=== Performance Benchmarks (Raw STM SkipList) ===" << std::endl;

        auto timer = []() {
            return std::chrono::high_resolution_clock::now();
        };
        auto elapsed_ms = [](auto start) {
            auto end = std::chrono::high_resolution_clock::now();
            return std::chrono::duration<double, std::milli>(end - start).count();
        };

        const int SMALL_N = 1000;
        const int LARGE_N = 10000;

        // Benchmark 1: Sequential insert
        {
            auto start = timer();
            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });
            for (int i = 0; i < LARGE_N; i++) {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), std::rand() % 16);
                });
            }
            std::cout << std::left << std::setw(30) << "Sequential insert (10000):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 2: Random insert
        {
            std::vector<unsigned int> keys(LARGE_N);
            for (int i = 0; i < LARGE_N; i++) keys[i] = std::rand();

            auto start = timer();
            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });
            for (int i = 0; i < LARGE_N; i++) {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, keys[i], keys[i] * 10, std::rand() % 16);
                });
            }
            std::cout << std::left << std::setw(30) << "Random insert (10000):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 3: Lookup
        {
            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });
            for (int i = 0; i < SMALL_N; i++) {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), std::rand() % 16);
                });
            }

            auto start = timer();
            for (int i = 0; i < LARGE_N; i++) {
                stm::atomically([&] {
                    sl->lookup(nat_lt, nat_eq, (unsigned int)(i % SMALL_N));
                });
            }
            std::cout << std::left << std::setw(30) << "Lookup (10000 ops):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 4: Member check
        {
            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });
            for (int i = 0; i < SMALL_N; i++) {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), std::rand() % 16);
                });
            }

            auto start = timer();
            for (int i = 0; i < LARGE_N; i++) {
                stm::atomically([&] {
                    sl->member(nat_lt, nat_eq, (unsigned int)(i % SMALL_N));
                });
            }
            std::cout << std::left << std::setw(30) << "Member (10000 ops):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 5: PopFront
        {
            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });
            for (int i = 0; i < SMALL_N; i++) {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), std::rand() % 16);
                });
            }

            auto start = timer();
            for (int i = 0; i < SMALL_N; i++) {
                stm::atomically([&] {
                    sl->popFront();
                });
            }
            std::cout << std::left << std::setw(30) << "PopFront (1000 ops):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 6: Concurrent insert (4 threads)
        {
            const int NUM_THREADS = 4;
            const int ITEMS_PER_THREAD = SMALL_N / NUM_THREADS;

            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });

            auto start = timer();
            std::vector<std::thread> threads;
            for (int t = 0; t < NUM_THREADS; t++) {
                threads.emplace_back([&sl, t, ITEMS_PER_THREAD]() {
                    std::mt19937 rng(t);  // Thread-local RNG
                    for (int i = 0; i < ITEMS_PER_THREAD; i++) {
                        unsigned int key = t * ITEMS_PER_THREAD + i;
                        unsigned int level = rng() % 16;
                        stm::atomically([&] {
                            sl->insert(nat_lt, nat_eq, key, key * 10, level);
                        });
                    }
                });
            }
            for (auto& th : threads) th.join();
            std::cout << std::left << std::setw(30) << "Concurrent insert (4T, 1000):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 7: Concurrent lookup (4 threads)
        {
            const int NUM_THREADS = 4;
            const int OPS_PER_THREAD = LARGE_N / NUM_THREADS;

            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });
            for (int i = 0; i < SMALL_N; i++) {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), std::rand() % 16);
                });
            }

            auto start = timer();
            std::vector<std::thread> threads;
            for (int t = 0; t < NUM_THREADS; t++) {
                threads.emplace_back([&sl, OPS_PER_THREAD, SMALL_N]() {
                    for (int i = 0; i < OPS_PER_THREAD; i++) {
                        stm::atomically([&] {
                            sl->lookup(nat_lt, nat_eq, (unsigned int)(i % SMALL_N));
                        });
                    }
                });
            }
            for (auto& th : threads) th.join();
            std::cout << std::left << std::setw(30) << "Concurrent lookup (4T, 10000):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 8: Mixed concurrent (2 writers, 2 readers)
        {
            const int OPS_PER_THREAD = SMALL_N / 2;

            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });
            // Pre-populate
            for (int i = 0; i < 100; i++) {
                stm::atomically([&] {
                    sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), i % 16);
                });
            }

            auto start = timer();
            std::vector<std::thread> threads;

            // 2 writer threads
            for (int t = 0; t < 2; t++) {
                threads.emplace_back([&sl, t, OPS_PER_THREAD]() {
                    std::mt19937 rng(100 + t);
                    for (int i = 0; i < OPS_PER_THREAD; i++) {
                        unsigned int key = 1000 + t * OPS_PER_THREAD + i;
                        unsigned int level = rng() % 16;
                        stm::atomically([&] {
                            sl->insert(nat_lt, nat_eq, key, key * 10, level);
                        });
                    }
                });
            }

            // 2 reader threads
            for (int t = 0; t < 2; t++) {
                threads.emplace_back([&sl, OPS_PER_THREAD]() {
                    for (int i = 0; i < OPS_PER_THREAD; i++) {
                        stm::atomically([&] {
                            sl->member(nat_lt, nat_eq, (unsigned int)(i % 100));
                        });
                    }
                });
            }

            for (auto& th : threads) th.join();
            std::cout << std::left << std::setw(30) << "Mixed concurrent (4T):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        // Benchmark 9: Producer-consumer
        {
            auto sl = stm::atomically([] {
                return SkipList<int, int>::template create<unsigned int, unsigned int>(0, 0);
            });

            std::atomic<bool> done{false};
            std::atomic<int> consumed{0};

            auto start = timer();

            std::thread producer([&]() {
                std::mt19937 rng(200);
                for (int i = 0; i < SMALL_N; i++) {
                    unsigned int level = rng() % 16;
                    stm::atomically([&, level] {
                        sl->insert(nat_lt, nat_eq, (unsigned int)i, (unsigned int)(i * 10), level);
                    });
                }
                done = true;
            });

            std::thread consumer([&]() {
                while (!done || consumed < SMALL_N) {
                    auto result = stm::atomically([&]() -> std::optional<std::pair<unsigned int, unsigned int>> {
                        return sl->popFront();
                    });
                    if (result.has_value()) {
                        consumed++;
                    } else {
                        std::this_thread::yield();
                    }
                }
            });

            producer.join();
            consumer.join();
            std::cout << std::left << std::setw(30) << "Producer-consumer (1000):"
                      << std::right << std::setw(10) << std::fixed << std::setprecision(2)
                      << elapsed_ms(start) << " ms" << std::endl;
        }

        std::cout << "==========================================" << std::endl;
    }

    return 0;
}
