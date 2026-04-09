// Port of all Rust tests from:
//   stm-core/src/tvar.rs
//   stm-core/src/transaction/mod.rs (test module)
//   stm-core/src/transaction/control_block.rs (test module)
//   stm-core/src/transaction/log_var.rs
//   stm-core/src/lib.rs (test_lib module)
//
// Minimal test harness — no external dependencies.

#include "stm.h"

#include <atomic>
#include <cassert>
#include <chrono>
#include <functional>
#include <future>
#include <iostream>
#include <optional>
#include <string>
#include <thread>
#include <vector>

// ---------- Test utilities (port of stm-core/src/test.rs) ----------
//
// The Rust version uses detached threads + mpsc channels. We mirror this
// with detached threads + a shared promise/atomic flag. std::async is
// unsuitable because its destructor joins the thread, blocking forever
// if the function doesn't terminate (which is the whole point of some tests).

/// Run f and g concurrently, return f's result or nullopt on timeout.
/// f runs in a detached thread. g runs in the calling thread.
/// Mirrors Rust's `test::async`.
template <typename T>
static std::optional<T> run_async(int duration_ms,
                                  std::function<T()> f,
                                  std::function<void()> g) {
    // Shared state: the result slot and a flag.
    auto result = std::make_shared<std::optional<T>>();
    auto done = std::make_shared<std::atomic<bool>>(false);
    auto mtx = std::make_shared<std::mutex>();
    auto cv = std::make_shared<std::condition_variable>();

    std::thread([=]() {
        T val = f();
        {
            std::lock_guard<std::mutex> lock(*mtx);
            *result = std::move(val);
            done->store(true);
        }
        cv->notify_one();
    }).detach();

    g();

    // Poll in 50ms steps, matching the Rust implementation.
    for (int elapsed = 0; elapsed < duration_ms; elapsed += 50) {
        {
            std::unique_lock<std::mutex> lock(*mtx);
            if (cv->wait_for(lock, std::chrono::milliseconds(50),
                             [&] { return done->load(); })) {
                return std::move(*result);
            }
        }
    }

    return std::nullopt;
}

/// Check if f terminates within duration_ms.
/// If it doesn't, the detached thread lives forever (same caveat as Rust).
static bool terminates(int duration_ms, std::function<void()> f) {
    // Wrap void->void into int->int for run_async.
    auto wrapped = [f_inner = std::move(f)]() -> int { f_inner(); return 0; };
    return run_async<int>(duration_ms, std::move(wrapped), [](){}).has_value();
}

/// Check if f terminates within duration_ms when g runs concurrently.
static bool terminates_async(int duration_ms,
                             std::function<void()> f,
                             std::function<void()> g) {
    auto wrapped = [f_inner = std::move(f)]() -> int { f_inner(); return 0; };
    return run_async<int>(duration_ms, std::move(wrapped), std::move(g)).has_value();
}

// ---------- Test runner ----------

static int tests_run = 0;
static int tests_passed = 0;
static int tests_failed = 0;

#define RUN_TEST(name)                                               \
    do {                                                              \
        tests_run++;                                                  \
        std::cout << "  " << #name << " ... " << std::flush;         \
        try {                                                         \
            name();                                                   \
            tests_passed++;                                           \
            std::cout << "ok" << std::endl;                           \
        } catch (const std::exception& e) {                           \
            tests_failed++;                                           \
            std::cout << "FAILED: " << e.what() << std::endl;        \
        } catch (...) {                                               \
            tests_failed++;                                           \
            std::cout << "FAILED (unknown exception)" << std::endl;  \
        }                                                             \
    } while (0)

#define ASSERT_EQ(a, b)                                              \
    do {                                                              \
        auto _a = (a); auto _b = (b);                                \
        if (_a != _b) {                                               \
            throw std::runtime_error(                                 \
                std::string(__FILE__) + ":" +                         \
                std::to_string(__LINE__) + ": " +                    \
                #a " != " #b);                                       \
        }                                                             \
    } while (0)

#define ASSERT_TRUE(x)                                               \
    do {                                                              \
        if (!(x)) {                                                   \
            throw std::runtime_error(                                 \
                std::string(__FILE__) + ":" +                         \
                std::to_string(__LINE__) + ": " #x " is false");     \
        }                                                             \
    } while (0)

#define ASSERT_FALSE(x)                                              \
    do {                                                              \
        if ((x)) {                                                    \
            throw std::runtime_error(                                 \
                std::string(__FILE__) + ":" +                         \
                std::to_string(__LINE__) + ": " #x " is true");      \
        }                                                             \
    } while (0)

using namespace stm;

// ==================== tvar.rs tests ====================

/// Port of `test_read_atomic`
void test_read_atomic() {
    TVar<int> var(42);
    ASSERT_EQ(42, var.read_atomic());
}

// ==================== log_var.rs tests ====================

/// Port of `test_write_obsolete_ignore`
void test_write_obsolete_ignore() {
    auto lv = detail::LogVar::make_write(std::make_shared<int>(42));
    auto result = std::move(lv).obsolete();
    ASSERT_TRUE(!result.has_value());
}

// ==================== control_block.rs tests ====================

/// Port of `blocked` — ControlBlock::wait should not terminate without set_changed.
void test_control_block_blocked() {
    auto ctrl = std::make_shared<detail::ControlBlock>();
    auto raw = ctrl.get();
    ASSERT_FALSE(terminates(100, [raw]() { raw->wait(); }));
}

/// Port of `wait_after_change` — should return immediately after set_changed.
void test_control_block_wait_after_change() {
    auto ctrl = std::make_shared<detail::ControlBlock>();
    ctrl->set_changed();
    auto raw = ctrl.get();
    ASSERT_TRUE(terminates(50, [raw]() { raw->wait(); }));
}

/// Port of `wait_after_multiple_changes` — multiple set_changed is idempotent.
void test_control_block_wait_after_multiple_changes() {
    auto ctrl = std::make_shared<detail::ControlBlock>();
    ctrl->set_changed();
    ctrl->set_changed();
    ctrl->set_changed();
    ctrl->set_changed();
    auto raw = ctrl.get();
    ASSERT_TRUE(terminates(50, [raw]() { raw->wait(); }));
}

/// Port of `wait_threaded_wakeup` — wakeup from another thread.
void test_control_block_wait_threaded_wakeup() {
    auto ctrl = std::make_shared<detail::ControlBlock>();
    auto ctrl2 = ctrl;
    auto raw = ctrl.get();
    auto raw2 = ctrl2.get();
    bool terminated = terminates_async(500,
        [raw]() { raw->wait(); },
        [raw2]() { raw2->set_changed(); });
    ASSERT_TRUE(terminated);
}

// ==================== transaction/mod.rs tests ====================

/// Port of `transaction_simple`
void test_transaction_simple() {
    int x = atomically([](Transaction&) { return 42; });
    ASSERT_EQ(x, 42);
}

/// Port of `transaction_read`
void test_transaction_read() {
    TVar<int> var(42);
    int x = atomically([&](Transaction& tx) {
        return var.read(tx);
    });
    ASSERT_EQ(x, 42);
}

/// Port of `transaction_write`
void test_transaction_write() {
    TVar<int> var(42);
    atomically([&](Transaction& tx) {
        var.write(tx, 0);
        return 0; // dummy return
    });
    ASSERT_EQ(var.read_atomic(), 0);
}

/// Port of `transaction_copy`
void test_transaction_copy() {
    TVar<int> read_var(42);
    TVar<int> write_var(0);

    atomically([&](Transaction& tx) {
        int r = read_var.read(tx);
        write_var.write(tx, r);
        return 0;
    });

    ASSERT_EQ(write_var.read_atomic(), 42);
}

/// Port of `read` (direct Transaction log test)
void test_transaction_log_read() {
    // This test in Rust directly constructs a Transaction.
    // We test the same behavior through atomically.
    TVar<std::vector<int>> var({1, 2, 3, 4});
    auto result = atomically([&](Transaction& tx) {
        return var.read(tx);
    });
    ASSERT_EQ(result, (std::vector<int>{1, 2, 3, 4}));
}

/// Port of `write_read` (write then read in same transaction)
void test_transaction_log_write_read() {
    TVar<std::vector<int>> var({1, 2});

    auto result = atomically([&](Transaction& tx) {
        var.write(tx, std::vector<int>{1, 2, 3, 4});
        return var.read(tx);
    });

    // Transaction should see the written value.
    ASSERT_EQ(result, (std::vector<int>{1, 2, 3, 4}));
    // Original is preserved until commit — but commit happened, so now it's updated.
    ASSERT_EQ(var.read_atomic(), (std::vector<int>{1, 2, 3, 4}));
}

/// Port of `transaction_with_control_abort_on_single_run`
void test_transaction_with_control_abort_on_single_run() {
    TVar<int> var(42);
    auto x = Transaction::with_control<int>(
        [](StmError) { return TransactionControl::Abort; },
        [&](Transaction& tx) { return var.read(tx); });
    ASSERT_EQ(x, std::optional<int>(42));
}

/// Port of `transaction_with_control_abort_on_retry`
void test_transaction_with_control_abort_on_retry() {
    auto x = Transaction::with_control<int>(
        [](StmError) { return TransactionControl::Abort; },
        [](Transaction&) -> int { retry<int>(); });
    ASSERT_EQ(x, std::nullopt);
}

/// Port of `transaction_nested_fail` — should throw/assert on nested atomically.
void test_transaction_nested_fail() {
    bool caught = false;
    try {
        atomically([](Transaction&) {
            atomically([](Transaction&) { return 42; });
            return 1;
        });
    } catch (...) {
        caught = true;
    }
    ASSERT_TRUE(caught);
}

// ==================== lib.rs tests ====================

/// Port of `infinite_retry`
void test_infinite_retry() {
    bool terminated = terminates(300, []() {
        atomically([](Transaction&) -> int {
            retry<int>();
        });
    });
    ASSERT_FALSE(terminated);
}

/// Port of `stm_nested`
void test_stm_nested() {
    TVar<int> var(0);
    int x = atomically([&](Transaction& tx) {
        var.write(tx, 42);
        return var.read(tx);
    });
    ASSERT_EQ(42, x);
}

/// Port of `threaded`
void test_threaded() {
    TVar<int> var(0);

    auto result = run_async<int>(800,
        [var]() mutable {
            return atomically([&var](Transaction& tx) -> int {
                int x = var.read(tx);
                if (x == 0) {
                    retry<int>();
                }
                return x;
            });
        },
        [&var]() {
            std::this_thread::sleep_for(std::chrono::milliseconds(100));
            atomically([&var](Transaction& tx) {
                var.write(tx, 42);
                return 0;
            });
        });

    ASSERT_TRUE(result.has_value());
    ASSERT_EQ(42, *result);
}

/// Port of `read_write_interfere`
void test_read_write_interfere() {
    TVar<int> var(0);

    auto t = std::thread([var]() mutable {
        atomically([&var](Transaction& tx) {
            int x = var.read(tx);
            std::this_thread::sleep_for(std::chrono::milliseconds(500));
            var.write(tx, x + 10);
            return 0;
        });
    });

    // Ensure thread has started and read the var.
    std::this_thread::sleep_for(std::chrono::milliseconds(100));

    // Change the var — this should cause the other thread's transaction to retry.
    atomically([&var](Transaction& tx) {
        var.write(tx, 32);
        return 0;
    });

    t.join();
    ASSERT_EQ(42, var.read_atomic());
}

/// Port of `or_simple`
void test_or_simple() {
    TVar<int> var(42);

    int x = atomically([&](Transaction& tx) {
        return tx.or_<int>(
            [](Transaction&) -> int { retry<int>(); },
            [&](Transaction& t) { return var.read(t); });
    });

    ASSERT_EQ(x, 42);
}

/// Port of `or_nocommit` — writes in failed branch should not be committed.
void test_or_nocommit() {
    TVar<int> var(42);

    int x = atomically([&](Transaction& tx) {
        return tx.or_<int>(
            [&](Transaction& t) -> int {
                var.write(t, 23);
                retry<int>();
            },
            [&](Transaction& t) { return var.read(t); });
    });

    ASSERT_EQ(x, 42);
}

/// Port of `or_nested_first`
void test_or_nested_first() {
    TVar<int> var(42);

    int x = atomically([&](Transaction& tx) {
        return tx.or_<int>(
            [](Transaction& t) -> int {
                return t.or_<int>(
                    [](Transaction&) -> int { retry<int>(); },
                    [](Transaction&) -> int { retry<int>(); });
            },
            [&](Transaction& t) { return var.read(t); });
    });

    ASSERT_EQ(x, 42);
}

/// Port of `or_nested_second`
void test_or_nested_second() {
    TVar<int> var(42);

    int x = atomically([&](Transaction& tx) {
        return tx.or_<int>(
            [](Transaction&) -> int { retry<int>(); },
            [&](Transaction& t) -> int {
                return t.or_<int>(
                    [&](Transaction& t2) { return var.read(t2); },
                    [](Transaction&) -> int { retry<int>(); });
            });
    });

    ASSERT_EQ(x, 42);
}

/// Port of `guard_true`
void test_guard_true() {
    // guard(true) should not throw.
    guard(true);
}

/// Port of `guard_false`
void test_guard_false() {
    bool caught = false;
    try {
        guard(false);
    } catch (StmError e) {
        ASSERT_EQ(e, StmError::Retry);
        caught = true;
    }
    ASSERT_TRUE(caught);
}

/// Port of `optionally_succeed`
void test_optionally_succeed() {
    auto x = atomically([](Transaction& t) {
        return optionally<int>(t, [](Transaction&) { return 42; });
    });
    ASSERT_EQ(x, std::optional<int>(42));
}

/// Port of `optionally_fail`
void test_optionally_fail() {
    auto x = atomically([](Transaction& t) {
        return optionally<int>(t, [](Transaction&) -> int { retry<int>(); });
    });
    ASSERT_EQ(x, std::nullopt);
}

/// Port of `unwrap_some`
void test_unwrap_some() {
    auto x = std::optional<int>(42);
    int y = atomically([&](Transaction&) {
        return unwrap_or_retry(x);
    });
    ASSERT_EQ(y, 42);
}

/// Port of `unwrap_none`
void test_unwrap_none() {
    std::optional<int> x = std::nullopt;
    bool caught = false;
    try {
        unwrap_or_retry(x);
    } catch (StmError e) {
        ASSERT_EQ(e, StmError::Retry);
        caught = true;
    }
    ASSERT_TRUE(caught);
}

// ==================== Main ====================

int main() {
    std::cout << "Running crane-stm tests..." << std::endl;

    std::cout << "\n--- TVar tests ---" << std::endl;
    RUN_TEST(test_read_atomic);

    std::cout << "\n--- LogVar tests ---" << std::endl;
    RUN_TEST(test_write_obsolete_ignore);

    std::cout << "\n--- ControlBlock tests ---" << std::endl;
    RUN_TEST(test_control_block_blocked);
    RUN_TEST(test_control_block_wait_after_change);
    RUN_TEST(test_control_block_wait_after_multiple_changes);
    RUN_TEST(test_control_block_wait_threaded_wakeup);

    std::cout << "\n--- Transaction tests ---" << std::endl;
    RUN_TEST(test_transaction_simple);
    RUN_TEST(test_transaction_read);
    RUN_TEST(test_transaction_write);
    RUN_TEST(test_transaction_copy);
    RUN_TEST(test_transaction_log_read);
    RUN_TEST(test_transaction_log_write_read);
    RUN_TEST(test_transaction_with_control_abort_on_single_run);
    RUN_TEST(test_transaction_with_control_abort_on_retry);
    RUN_TEST(test_transaction_nested_fail);

    std::cout << "\n--- STM API tests ---" << std::endl;
    RUN_TEST(test_infinite_retry);
    RUN_TEST(test_stm_nested);
    RUN_TEST(test_threaded);
    RUN_TEST(test_read_write_interfere);
    RUN_TEST(test_or_simple);
    RUN_TEST(test_or_nocommit);
    RUN_TEST(test_or_nested_first);
    RUN_TEST(test_or_nested_second);
    RUN_TEST(test_guard_true);
    RUN_TEST(test_guard_false);
    RUN_TEST(test_optionally_succeed);
    RUN_TEST(test_optionally_fail);
    RUN_TEST(test_unwrap_some);
    RUN_TEST(test_unwrap_none);

    std::cout << "\n==============================" << std::endl;
    std::cout << tests_run << " tests run, "
              << tests_passed << " passed, "
              << tests_failed << " failed." << std::endl;

    return tests_failed > 0 ? 1 : 0;
}
