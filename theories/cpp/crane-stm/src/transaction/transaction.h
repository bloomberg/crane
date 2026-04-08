#pragma once

// Port of stm-core/src/transaction/mod.rs

#include <cassert>
#include <functional>
#include <map>
#include <memory>
#include <optional>
#include <vector>

#include "../result.h"
#include "../tvar.h"
#include "control_block.h"
#include "log_var.h"

namespace stm {

/// Mirrors Rust's `TransactionControl` enum.
enum class TransactionControl {
    Retry,
    Abort,
};

/// Transaction tracks all read and written variables.
/// Mirrors Rust's `Transaction` struct.
class Transaction {
public:
    /// Run a function atomically. Equivalent to Rust's `Transaction::with`.
    /// Retries on failure/conflict, blocks on retry until a read var changes.
    ///
    /// Because C++ lacks Rust's `?` operator, the user function returns T directly
    /// and signals retry/failure by throwing StmError (caught internally).
    template <typename T, typename F>
    static T with(F&& f) {
        auto result = with_control<T>(
            [](StmError) { return TransactionControl::Retry; },
            std::forward<F>(f));
        // with Retry control, result is always present
        return std::move(*result);
    }

    /// Run with a control function that can abort on errors.
    /// Mirrors Rust's `Transaction::with_control`.
    template <typename T, typename F, typename C>
    static std::optional<T> with_control(C&& control, F&& f) {
        TransactionGuard guard;

        Transaction transaction;

        while (true) {
            try {
                T result = f(transaction);
                if (transaction.commit()) {
                    return result;
                }
            } catch (StmError e) {
                if (control(e) == TransactionControl::Abort) {
                    return std::nullopt;
                }
                if (e == StmError::Retry) {
                    transaction.wait_for_change();
                }
            }

            transaction.clear();
        }
    }

    /// Read a variable within the transaction.
    /// Mirrors Rust's `Transaction::read`.
    template <typename T>
    T read(const TVar<T>& var) {
        auto ctrl = var.control_block();
        auto it = vars_.find(ctrl);

        ArcAny value;
        if (it != vars_.end()) {
            // Variable accessed before — read from log.
            value = it->second.read();
        } else {
            // First access — read from the variable.
            value = var.read_ref_atomic();
            vars_.emplace(ctrl, detail::LogVar::make_read(value));
        }

        return *std::static_pointer_cast<T>(value);
    }

    /// Write a variable within the transaction.
    /// Mirrors Rust's `Transaction::write`.
    template <typename T>
    void write(const TVar<T>& var, T value) {
        auto boxed = std::static_pointer_cast<void>(
            std::make_shared<T>(std::move(value)));

        auto ctrl = var.control_block();
        auto it = vars_.find(ctrl);

        if (it != vars_.end()) {
            it->second.write(std::move(boxed));
        } else {
            vars_.emplace(ctrl, detail::LogVar::make_write(std::move(boxed)));
        }
    }

    /// Combine two computations. If the first retries, run the second.
    /// If both retry, wait on TVars from both.
    /// Mirrors Rust's `Transaction::or`.
    template <typename T, typename F1, typename F2>
    T or_(F1&& first, F2&& second) {
        // Backup the current log.
        auto backup_vars = vars_;

        try {
            return first(*this);
        } catch (StmError e) {
            if (e == StmError::Retry) {
                // Swap — restore the original log as current.
                auto failed_vars = std::move(vars_);
                vars_ = std::move(backup_vars);

                try {
                    T result = second(*this);
                    // Merge the failed branch's reads for blocking purposes.
                    combine(std::move(failed_vars));
                    return result;
                } catch (StmError e2) {
                    if (e2 == StmError::Failure) {
                        throw; // Propagate failure.
                    }
                    // Both retried — merge reads and propagate retry.
                    combine(std::move(failed_vars));
                    throw;
                }
            }
            throw; // Propagate failure from first.
        }
    }

private:
    using VarMap = std::map<std::shared_ptr<VarControlBlock>,
                            detail::LogVar, VarControlBlockPtrCmp>;
    VarMap vars_;

    Transaction() = default;

    /// Clear the transaction log before retrying.
    void clear() {
        vars_.clear();
    }

    /// Merge reads from a failed `or` branch for blocking purposes.
    /// Mirrors Rust's `Transaction::combine`.
    void combine(VarMap other) {
        for (auto& [var, value] : other) {
            auto obsolete = std::move(value).obsolete();
            if (obsolete && vars_.find(var) == vars_.end()) {
                vars_.emplace(var, std::move(*obsolete));
            }
        }
    }

    /// Wait for any read variable to change.
    /// Mirrors Rust's `Transaction::wait_for_change`.
    void wait_for_change() {
        auto ctrl = std::make_shared<detail::ControlBlock>();

        // Move vars out (mirrors Rust's mem::replace).
        VarMap vars = std::move(vars_);
        vars_ = VarMap{};

        std::vector<std::shared_ptr<VarControlBlock>> reads;

        bool blocking = true;
        for (auto& [var, log_var] : vars) {
            auto read_val = std::move(log_var).into_read_value();
            if (!read_val) continue;

            var->wait(ctrl);

            // Check consistency: has the value changed since we read it?
            {
                std::shared_lock<std::shared_mutex> lock(var->value_mutex_);
                if (lock && var->value_.get() != read_val->get()) {
                    blocking = false;
                }
            }
            reads.push_back(var);

            if (!blocking) break;
        }

        if (blocking) {
            ctrl->wait();
        }

        // Mark control blocks as dead.
        for (auto& var : reads) {
            var->set_dead();
        }
    }

    /// Commit the transaction log.
    /// Two-phase locking: acquire locks in address order, check read consistency,
    /// write back, wake waiters.
    /// Mirrors Rust's `Transaction::commit`.
    bool commit() {
        // Phase 1: Acquire locks and check consistency.

        // RAII wrappers for the locks we acquire.
        std::vector<std::shared_lock<std::shared_mutex>> read_locks;
        std::vector<std::unique_lock<std::shared_mutex>> write_locks;

        // Track which values to write and which vars were written.
        struct WriteEntry {
            ArcAny value;
            size_t lock_index; // index into write_locks
        };
        std::vector<WriteEntry> writes;
        std::vector<std::shared_ptr<VarControlBlock>> written_vars;

        for (auto& [var, log_var] : vars_) {
            auto& v = log_var.variant();

            if (auto* w = std::get_if<detail::Write>(&v)) {
                std::unique_lock<std::shared_mutex> lock(var->value_mutex_);
                size_t idx = write_locks.size();
                write_locks.push_back(std::move(lock));
                writes.push_back({w->value, idx});
                written_vars.push_back(var);

            } else if (auto* row = std::get_if<detail::ReadObsoleteWrite>(&v)) {
                std::unique_lock<std::shared_mutex> lock(var->value_mutex_);
                size_t idx = write_locks.size();
                write_locks.push_back(std::move(lock));
                writes.push_back({row->value, idx});
                written_vars.push_back(var);

            } else if (auto* rw = std::get_if<detail::ReadWrite>(&v)) {
                std::unique_lock<std::shared_mutex> lock(var->value_mutex_);
                // Check consistency: original must still be current.
                if (var->value_.get() != rw->original.get()) {
                    return false;
                }
                size_t idx = write_locks.size();
                write_locks.push_back(std::move(lock));
                writes.push_back({rw->value, idx});
                written_vars.push_back(var);

            } else if (std::holds_alternative<detail::ReadObsolete>(v)) {
                // Nothing to do — only needed for blocking, not consistency.

            } else if (auto* r = std::get_if<detail::Read>(&v)) {
                std::shared_lock<std::shared_mutex> lock(var->value_mutex_);
                // Check consistency.
                if (var->value_.get() != r->value.get()) {
                    return false;
                }
                read_locks.push_back(std::move(lock));
            }
        }

        // Phase 2: Write back and release.

        // Release reads first (mirrors Rust: `drop(read_vec)`).
        read_locks.clear();

        // Write values while still holding write locks.
        {
            size_t write_idx = 0;
            for (auto& [var, log_var] : vars_) {
                auto& v = log_var.variant();
                if (std::holds_alternative<detail::Write>(v) ||
                    std::holds_alternative<detail::ReadObsoleteWrite>(v) ||
                    std::holds_alternative<detail::ReadWrite>(v)) {
                    var->value_ = writes[write_idx].value;
                    write_idx++;
                }
            }
        }

        // Release write locks before waking (implicit via clear).
        write_locks.clear();

        // Wake all threads waiting on written vars.
        for (auto& var : written_vars) {
            var->wake_all();
        }

        return true;
    }

    /// RAII guard that prevents nested transactions.
    /// Mirrors Rust's `TransactionGuard`.
    struct TransactionGuard {
        TransactionGuard() {
            if (running()) {
                throw std::logic_error("STM: Nested Transaction");
            }
            running() = true;
        }
        ~TransactionGuard() {
            running() = false;
        }
        TransactionGuard(const TransactionGuard&) = delete;
        TransactionGuard& operator=(const TransactionGuard&) = delete;

    private:
        static bool& running() {
            thread_local bool r = false;
            return r;
        }
    };
};

// Definitions of TVar<T>::read and TVar<T>::write that depend on Transaction.
template <typename T>
T TVar<T>::read(Transaction& tx) const {
    return tx.read(*this);
}

template <typename T>
void TVar<T>::write(Transaction& tx, T value) const {
    tx.write(*this, std::move(value));
}

} // namespace stm
