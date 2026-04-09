#pragma once

// Port of stm-core/src/tvar.rs

#include <bsl_algorithm.h>
#include <bsl_atomic.h>
#include <bsl_cassert.h>
#include <bsl_cstddef.h>
#include <bsl_memory.h>
#include <bsl_mutex.h>
#include <bsl_shared_mutex.h>
#include <bsl_utility.h>
#include <bsl_vector.h>

#include "transaction/control_block.h"
#include "transaction/log_var.h"

namespace stm {

// Forward declaration.
class Transaction;

/// VarControlBlock contains all the internal data for a TVar.
/// Mirrors the Rust `VarControlBlock` struct exactly.
///
/// The control block is accessed from other threads directly whereas
/// TVar<T> is just a type-safe wrapper around it.
class VarControlBlock {
public:
    template <typename T>
    static bsl::shared_ptr<VarControlBlock> create(T val) {
        auto cb = bsl::make_shared<VarControlBlock>();
        cb->value_ = bsl::make_shared<T>(bsl::move(val));
        return cb;
    }

    VarControlBlock() : dead_threads_(0) {}

    // Non-copyable (identity is pointer-based, same as Rust).
    VarControlBlock(const VarControlBlock&) = delete;
    VarControlBlock& operator=(const VarControlBlock&) = delete;

    /// Wake all threads waiting for this variable to change.
    /// Mirrors Rust's `wake_all`.
    void wake_all() {
        // Atomically take all waiting threads.
        bsl::vector<bsl::weak_ptr<detail::ControlBlock>> threads;
        {
            bsl::lock_guard<bsl::mutex> lock(waiters_mutex_);
            threads.swap(waiting_threads_);
        }

        // Wake all that are still alive.
        for (auto& weak : threads) {
            if (auto ctrl = weak.lock()) {
                ctrl->set_changed();
            }
        }
    }

    /// Register a thread to be woken when this variable changes.
    /// Mirrors Rust's `wait`.
    void wait(const bsl::shared_ptr<detail::ControlBlock>& ctrl) {
        bsl::lock_guard<bsl::mutex> lock(waiters_mutex_);
        waiting_threads_.push_back(ctrl);
    }

    /// Mark a control block as dead. If too many dead threads accumulate,
    /// perform cleanup. Mirrors Rust's `set_dead` (threshold = 64).
    void set_dead() {
        size_t deads = dead_threads_.fetch_add(1, bsl::memory_order_relaxed);

        if (deads >= 64) {
            bsl::lock_guard<bsl::mutex> lock(waiters_mutex_);
            dead_threads_.store(0, bsl::memory_order_seq_cst);

            // Remove all dead weak pointers.
            waiting_threads_.erase(
                bsl::remove_if(waiting_threads_.begin(), waiting_threads_.end(),
                    [](const bsl::weak_ptr<detail::ControlBlock>& w) {
                        return w.expired();
                    }),
                waiting_threads_.end());
        }
    }

    /// Read the value under a shared (read) lock.
    /// Returns a clone of the shared_ptr<void>.
    ArcAny read_value() const {
        bsl::shared_lock<bsl::shared_mutex> lock(value_mutex_);
        return value_;
    }

    /// Write the value under an exclusive (write) lock.
    void write_value(ArcAny new_val) {
        bsl::unique_lock<bsl::shared_mutex> lock(value_mutex_);
        value_ = bsl::move(new_val);
    }

    /// Get raw pointer address for ordering (mirrors Rust's `get_address`).
    uintptr_t get_address() const {
        return reinterpret_cast<uintptr_t>(this);
    }

private:
    bsl::mutex waiters_mutex_;
    bsl::vector<bsl::weak_ptr<detail::ControlBlock>> waiting_threads_;
    bsl::atomic<size_t> dead_threads_;

    mutable bsl::shared_mutex value_mutex_;
    ArcAny value_;

    // Transaction needs direct access for commit logic (lock acquisition).
    friend class Transaction;
};

/// Comparator for shared_ptr<VarControlBlock> that orders by raw pointer address.
/// This mirrors Rust's Ord impl on VarControlBlock (address-based ordering)
/// and ensures deterministic lock acquisition order to prevent deadlocks.
struct VarControlBlockPtrCmp {
    bool operator()(const bsl::shared_ptr<VarControlBlock>& a,
                    const bsl::shared_ptr<VarControlBlock>& b) const {
        return a->get_address() < b->get_address();
    }
};


/// A transactional variable that can be used in STM blocks.
/// Type-safe wrapper around VarControlBlock, mirroring Rust's `TVar<T>`.
///
/// T must be copyable (mirrors Rust's Clone bound).
template <typename T>
class TVar {
public:
    explicit TVar(T val)
        : control_block_(VarControlBlock::create(bsl::move(val))) {}

    /// Read atomically without a transaction.
    /// Returns a copy of the current value.
    /// Mirrors Rust's `read_atomic`.
    T read_atomic() const {
        auto val = read_ref_atomic();
        return *bsl::static_pointer_cast<T>(val);
    }

    /// Read atomically returning a type-erased shared_ptr.
    /// Mirrors Rust's `read_ref_atomic`.
    ArcAny read_ref_atomic() const {
        return control_block_->read_value();
    }

    // read() and write() are declared here but defined after Transaction
    // is fully defined, to break the circular dependency.
    // See stm.h for the definitions.

    /// Read within a transaction.
    T read(Transaction& tx) const;

    /// Write within a transaction.
    void write(Transaction& tx, T value) const;

    /// Modify the content with a function.
    /// Mirrors Rust's `TVar::modify`.
    template <typename F>
    void modify(Transaction& tx, F&& f) const {
        T old = read(tx);
        write(tx, f(bsl::move(old)));
    }

    /// Replace the value, returning the old one.
    /// Mirrors Rust's `TVar::replace`.
    T replace(Transaction& tx, T value) const {
        T old = read(tx);
        write(tx, bsl::move(value));
        return old;
    }

    /// Check if two TVars refer to the same location.
    /// Mirrors Rust's `TVar::ref_eq`.
    static bool ref_eq(const TVar& a, const TVar& b) {
        return a.control_block_ == b.control_block_;
    }

    /// Access the control block (internal use).
    const bsl::shared_ptr<VarControlBlock>& control_block() const {
        return control_block_;
    }

private:
    bsl::shared_ptr<VarControlBlock> control_block_;
};

} // namespace stm
