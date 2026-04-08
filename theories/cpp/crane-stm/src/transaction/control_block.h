#pragma once

// Port of stm-core/src/transaction/control_block.rs
//
// Rust uses thread::park/unpark for blocking. C++ lacks direct equivalents,
// so we use mutex + condition_variable to achieve identical semantics:
// - wait() blocks until set_changed() is called
// - set_changed() wakes the blocked thread (at most once)
// - The atomic bool prevents missed wakeups (same as Rust)

#include <atomic>
#include <condition_variable>
#include <mutex>

namespace stm {
namespace detail {

/// A control block for a currently running STM instance.
///
/// STM blocks on all read variables if retry was called.
/// This control block lets vars inform the STM instance of changes.
class ControlBlock {
public:
    ControlBlock() : blocked_(true) {}

    // Non-copyable, non-movable (matches Rust — used only via shared_ptr).
    ControlBlock(const ControlBlock&) = delete;
    ControlBlock& operator=(const ControlBlock&) = delete;

    /// Inform the control block that a variable has changed.
    /// Only wakes the thread once (atomic swap prevents redundant wakeups).
    void set_changed() {
        // Only wakeup once — mirrors `self.blocked.swap(false, SeqCst)`
        if (blocked_.exchange(false, std::memory_order_seq_cst)) {
            std::lock_guard<std::mutex> lock(mutex_);
            cv_.notify_one();
        }
    }

    /// Block until set_changed() is called.
    /// May return immediately if set_changed() was already called.
    void wait() {
        std::unique_lock<std::mutex> lock(mutex_);
        // Mirrors Rust's `while self.blocked.load(SeqCst) { thread::park(); }`
        cv_.wait(lock, [this] {
            return !blocked_.load(std::memory_order_seq_cst);
        });
    }

private:
    std::atomic<bool> blocked_;
    std::mutex mutex_;
    std::condition_variable cv_;
};

} // namespace detail
} // namespace stm
