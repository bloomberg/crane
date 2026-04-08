#pragma once

// STM adapter (BDE flavor): provides a mini_stm.h-compatible API on top of
// crane-stm.
//
// The Crane extraction system generates code where read/write calls have no
// explicit Transaction& parameter (the monadic extraction can't thread one
// through).  This header bridges the gap by storing the active Transaction in
// a thread-local, set/cleared by the no-parameter overload of atomically().

#include "crane-stm/src/stm.h"

#include <bsl_cassert.h>
#include <bsl_utility.h>

namespace stm {

// ---- Thread-local transaction management -----------------------------------

namespace compat {

inline thread_local Transaction* g_tx = nullptr;

inline Transaction& current_tx() {
    assert(g_tx != nullptr && "Must be called inside atomically()");
    return *g_tx;
}

// RAII guard that sets/clears the thread-local transaction pointer.
// Exception-safe: if the user function throws (e.g. retry()), the destructor
// still clears g_tx before Transaction::with_control catches the exception.
struct TxScope {
    explicit TxScope(Transaction& tx) noexcept { g_tx = &tx; }
    ~TxScope() noexcept { g_tx = nullptr; }
    TxScope(const TxScope&) = delete;
    TxScope& operator=(const TxScope&) = delete;
};

} // namespace compat

// ---- Free functions matching extraction patterns ----------------------------

/// Create a new TVar (value-based; TVar is internally reference-counted).
template <typename T>
TVar<T> newTVar(T init) {
    return TVar<T>(bsl::move(init));
}

/// Read a TVar using the implicit thread-local transaction.
template <typename T>
T readTVar(const TVar<T>& tv) {
    return tv.read(compat::current_tx());
}

/// Write a TVar using the implicit thread-local transaction.
template <typename T>
void writeTVar(const TVar<T>& tv, T val) {
    tv.write(compat::current_tx(), bsl::move(val));
}

// ---- No-parameter atomically overload --------------------------------------
//
// crane-stm's atomically(F) requires F(Transaction&).  The extraction
// generates lambdas with no parameters, e.g.:
//
//   stm::atomically([&] { return stm_basic_counter({}); });
//
// SFINAE picks this overload when the lambda takes no arguments, and
// crane-stm's overload when it takes Transaction&.

template <typename F>
auto atomically(F&& f) -> decltype(f()) {
    using R = decltype(f());
    return Transaction::with<R>([&](Transaction& tx) -> R {
        compat::TxScope scope(tx);
        return f();
    });
}

// ---- orElse for eagerly-evaluated values ------------------------------------
//
// The extraction generates:
//
//   stm::orElse<unsigned int>(stm_dequeue(q), 42u)
//
// Both arguments are evaluated eagerly (C++ function-call semantics).
// We wrap them in lambdas for Transaction::or_.
//
// Note: if the first argument calls retry(), the exception propagates before
// orElse is reached.  This matches mini_stm.h's behavior.

template <typename A>
A orElse(A left, A right) {
    auto& tx = compat::current_tx();
    return tx.template or_<A>(
        [left](Transaction&) -> A { return left; },
        [right](Transaction&) -> A { return right; });
}

} // namespace stm
