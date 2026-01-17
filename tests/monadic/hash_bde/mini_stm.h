// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#pragma once

// BDE equivalents
#include <bsl_atomic.h>
#include <bsl_chrono.h>
#include <bsl_condition_variable.h>
#include <bsl_concepts.h>
#include <bsl_cstdint.h>
#include <bsl_functional.h>
#include <bsl_mutex.h>
#include <bsl_thread.h>
#include <bsl_type_traits.h>
#include <bsl_unordered_map.h>
#include <bsl_utility.h>
#include <bsl_vector.h>
#include <bsl_algorithm.h>
#include <bsl_memory.h>
#include <bsls_assert.h>

namespace stm {

struct TVarBase;
struct TxAbortRetry final {};
struct TxAbortConflict final {};

template <typename FLeft, typename FRight>
concept SameReturn = bsl::invocable<FLeft&> && bsl::invocable<FRight&> &&
                     bsl::same_as<bsl::invoke_result_t<FLeft&>, bsl::invoke_result_t<FRight&>>;

struct TVarBase : public bsl::enable_shared_from_this<TVarBase> {
    bsl::atomic<uint64_t> version{0};
    mutable bsl::mutex m;
    bsl::condition_variable cv;
    virtual ~TVarBase() = default;
    virtual void publish_boxed(bsl::shared_ptr<void> boxed) = 0;
};

template <typename T>
struct TVar : TVarBase {
    // Strong exception-safety for commit:
    // Require nothrow move + nothrow swap so publish_boxed can't break atomicity.
    static_assert(bsl::is_nothrow_move_constructible_v<T>,
                  "T must be nothrow move constructible for STM commit strong exception safety");
    static_assert(bsl::is_nothrow_swappable_v<T>,
                  "T must be nothrow swappable for STM commit strong exception safety");

    T value;

    explicit TVar(T v) : value(bsl::move(v)) {}

    void publish_boxed(bsl::shared_ptr<void> boxed) override {
        // Called with tv.m held by the caller.
        T tmp = bsl::move(*static_cast<T*>(boxed.get())); // assumes nothrow move-constructible
        using bsl::swap;
        swap(value, tmp); // assumes nothrow swappable
        version.fetch_add(1, bsl::memory_order_release);
        cv.notify_all();
    }
};

struct Transaction {
    bsl::unordered_map<TVarBase*, uint64_t> readSet;
    bsl::unordered_map<TVarBase*, bsl::shared_ptr<void>> staged;
    bsl::vector<bsl::shared_ptr<TVarBase>> keepAlive;
    bool wantsRetry = false;
    void reset() {
        readSet.clear();
        staged.clear();
        keepAlive.clear();
        wantsRetry = false;
    }
};

inline thread_local Transaction* g_tx = nullptr;

// RAII: ensure g_tx is always cleared, even on exceptions.
struct TxScope {
    explicit TxScope(Transaction& t) noexcept { g_tx = &t; }
    ~TxScope() noexcept { g_tx = nullptr; }
    TxScope(const TxScope&) = delete;
    TxScope& operator=(const TxScope&) = delete;
};

namespace detail {
    template <class T>
    inline bsl::shared_ptr<void> box(T&& v) {
        return bsl::shared_ptr<void>(new bsl::decay_t<T>(bsl::forward<T>(v)),
                                     [](void* p){ delete static_cast<bsl::decay_t<T>*>(p); });
    }
    template <class T>
    inline T& unbox_ref(const bsl::shared_ptr<void>& p) {
        return *static_cast<T*>(p.get());
    }
    inline void track_keepalive(Transaction& tx, const bsl::shared_ptr<TVarBase>& sp) {
        auto* raw = sp.get();
        for (auto const& held : tx.keepAlive) if (held.get() == raw) return;
        tx.keepAlive.push_back(sp);
    }
}

template <typename T>
inline bsl::shared_ptr<TVar<T>> newTVar(T init) {
    return bsl::make_shared<TVar<T>>(bsl::move(init));
}

template <typename T>
inline T readTVarIO(const TVar<T>& tv) {
    bsl::lock_guard<bsl::mutex> lk(tv.m);
    return tv.value;
}

// ---- STM API ONLY via shared_ptr to avoid shared_from_this() UB on stack TVars ----

template <typename T>
inline T readTVar(const bsl::shared_ptr<TVar<T>>& tv) {
    BSLS_ASSERT(g_tx && "readTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, bsl::static_pointer_cast<TVarBase>(tv));

    // Read-your-own-writes: return staged value if present
    if (auto it = tx.staged.find(tv.get()); it != tx.staged.end()) {
        return detail::unbox_ref<T>(it->second);
    }

    // Coherent read under lock; record version while holding lock
    bsl::unique_lock<bsl::mutex> lk(tv->m);
    T result = tv->value; // copy
    uint64_t ver = tv->version.load(bsl::memory_order_acquire);
    tx.readSet.emplace(tv.get(), ver);
    return result;
}

template <typename T>
inline void writeTVar(const bsl::shared_ptr<TVar<T>>& tv, T newVal) {
    BSLS_ASSERT(g_tx && "writeTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, bsl::static_pointer_cast<TVarBase>(tv));

    // On first touch of this TVar, record its current version in the read-set
    if (tx.readSet.find(tv.get()) == tx.readSet.end()) {
        bsl::unique_lock<bsl::mutex> lk(tv->m);
        uint64_t ver = tv->version.load(bsl::memory_order_acquire);
        tx.readSet.emplace(tv.get(), ver);
    }

    // Stage the new value (overwrites previous staging if any)
    tx.staged[tv.get()] = detail::box(bsl::move(newVal));
}

// ---- retry / orElse ----

template <typename T>
[[noreturn]] inline T retry() {
    BSLS_ASSERT(g_tx && "retry() must be called inside atomically()");
    g_tx->wantsRetry = true;
    throw TxAbortRetry{};
}

template <typename FLeft, typename FRight>
requires SameReturn<FLeft, FRight>
auto orElse_helper(FLeft&& left, FRight&& right) -> bsl::invoke_result_t<FLeft&> {
    using R = bsl::invoke_result_t<FLeft&>;
    BSLS_ASSERT(g_tx && "orElse must be called inside atomically()");
    Transaction& tx = *g_tx;

    auto savedRead     = tx.readSet;
    auto savedStaged   = tx.staged;
    auto savedKeep     = tx.keepAlive;

    try {
        return static_cast<R>(left());
    } catch (const TxAbortRetry&) {
        tx.readSet   = bsl::move(savedRead);
        tx.staged    = bsl::move(savedStaged);
        tx.keepAlive = bsl::move(savedKeep);

        auto savedRead2 = tx.readSet; // for merge on double-retry
        try {
            return static_cast<R>(right());
        } catch (const TxAbortRetry&) {
            // Merge read sets so waking on either side can proceed
            for (auto& kv : savedRead2) tx.readSet.emplace(kv.first, kv.second);
            throw;
        }
    }
}

/*
hides the real semantic distinction between STM actions and pure values,
so chatGPT would only use it as a temporary hack.
*/
template <typename A>
auto orElse(A leftVal, A rightVal) {
  return orElse_helper([=]{ return leftVal; }, [=]{ return rightVal; });
}

// ---- atomically ----

template <typename F>
decltype(auto) atomically(F&& action) {
    using R = bsl::invoke_result_t<F&>;
    // Forbid nested transactions with a single g_tx pointer.
    BSLS_ASSERT(g_tx == nullptr && "Nested atomically() not supported");

    Transaction tx;

    for (;;) {
        tx.reset();
        TxScope scope(tx); // RAII: sets g_tx, clears on scope exit

        try {
            // Commit routine shared by both branches.
            auto commit = [&] {
                // Determine writer set and lock in a total order to avoid deadlocks
                bsl::vector<TVarBase*> writers;
                writers.reserve(tx.staged.size());
                for (auto& kv : tx.staged) writers.push_back(kv.first);
                bsl::sort(writers.begin(), writers.end());
                writers.erase(bsl::unique(writers.begin(), writers.end()), writers.end());

                bsl::vector<bsl::unique_lock<bsl::mutex>> held;
                held.reserve(writers.size());
                for (auto* tv : writers) held.emplace_back(tv->m);

                // Validate read set (writers are locked; non-writers can change and will cause abort)
                for (auto& kv : tx.readSet) {
                    TVarBase* tv = kv.first;
                    uint64_t seen = kv.second;
                    uint64_t cur = tv->version.load(bsl::memory_order_acquire);
                    if (cur != seen) {
                        held.clear();
                        throw TxAbortConflict{};
                    }
                }

                // Publish staged writes (no-throw by construction)
                for (auto* tv : writers) {
                    if (auto it = tx.staged.find(tv); it != tx.staged.end()) {
                        tv->publish_boxed(it->second);
                    }
                }
            };

            if constexpr (bsl::is_void_v<R>) {
                // Void-returning action
                action();
                commit();
                return; // return void
            } else {
                // Non-void action
                R result = action();
                commit();
                return result;
            }
        }
        catch (const TxAbortRetry&) {
            // Wait for *one* TVar from readSet to change to avoid indefinite blocking
            if (!tx.readSet.empty()) {
                auto it = tx.readSet.begin(); // arbitrary choice; could be random/heuristic
                TVarBase* tv = it->first;
                uint64_t seen = it->second;
                bsl::unique_lock<bsl::mutex> lk(tv->m);
                tv->cv.wait(lk, [&]{ return tv->version.load(bsl::memory_order_acquire) != seen; });
            } else {
                // No reads; just yield to avoid hot-spinning forever
                bsl::this_thread::yield();
            }
            // loop and retry
        }
        catch (const TxAbortConflict&) {
            // Simple backoff to reduce livelock risk
            bsl::this_thread::yield();
        }
        // Any other exception will unwind; TxScope clears g_tx, and the exception propagates.
    }
}

/*
// Exact function pointer: R (*)()
template <typename T>
inline T atomically(T (*fp)()) {
    return atomically([=]{ return fp(); });
}

// bsl::function<R()>
template <typename T>
inline T atomically(const bsl::function<T()>& f) {
    return atomically([&]{ return f(); });
}
*/

} // namespace stm
