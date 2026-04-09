#pragma once

// Port of stm-core/src/lib.rs and src/lib.rs (re-export facade)
//
// Top-level header that includes everything and provides the
// free functions: atomically, retry, guard, unwrap_or_retry, optionally.

#include <bsl_utility.h>

#include "result.h"
#include "tvar.h"
#include "transaction/transaction.h"

namespace stm {

/// Abort the current transaction and retry.
/// Blocks until at least one read variable has changed.
/// Mirrors Rust's `retry()`.
///
/// In C++ this throws StmError::Retry, which is caught by the
/// transaction loop. The user never sees the exception.
template <typename T = void>
[[noreturn]] T retry() {
    throw StmError::Retry;
}

/// Run a function atomically using Software Transactional Memory.
/// Mirrors Rust's `atomically`.
///
/// The function f receives a Transaction& and returns T directly.
/// Call retry() to block/retry. Throw StmError::Failure to force re-execution.
template <typename F>
auto atomically(F&& f) -> decltype(f(bsl::declval<Transaction&>())) {
    using T = decltype(f(bsl::declval<Transaction&>()));
    return Transaction::with<T>(bsl::forward<F>(f));
}

/// Retry until `cond` is true.
/// Mirrors Rust's `guard`.
inline void guard(bool cond) {
    if (!cond) {
        retry();
    }
}

/// Unwrap an optional or retry if it is empty.
/// Mirrors Rust's `unwrap_or_retry`.
template <typename T>
T unwrap_or_retry(bsl::optional<T> opt) {
    if (opt) {
        return bsl::move(*opt);
    }
    retry<T>();
}

/// Optionally run a transaction. If it retries, return nullopt instead
/// of cancelling the whole transaction.
/// Mirrors Rust's `optionally`.
template <typename T, typename F>
bsl::optional<T> optionally(Transaction& tx, F&& f) {
    return tx.or_<bsl::optional<T>>(
        [&](Transaction& t) -> bsl::optional<T> {
            return f(t);
        },
        [](Transaction&) -> bsl::optional<T> {
            return bsl::nullopt;
        });
}

} // namespace stm
