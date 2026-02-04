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
    virtual void commit_write(void* staged_ptr) = 0;
};

template <typename T>
struct TVar : TVarBase {
    static_assert(bsl::is_nothrow_move_constructible_v<T>,
                  "T must be nothrow move constructible for STM commit strong exception safety");
    static_assert(bsl::is_nothrow_swappable_v<T>,
                  "T must be nothrow swappable for STM commit strong exception safety");

    T value;

    explicit TVar(T v) : value(bsl::move(v)) {}

    void commit_write(void* staged_ptr) override {
        T* staged = static_cast<T*>(staged_ptr);
        using bsl::swap;
        swap(value, *staged);
        version.fetch_add(1, bsl::memory_order_release);
        cv.notify_all();
    }

    // Lock-free read of current value (caller handles validation)
    T read_value() const {
        return value;
    }
};

// Staged write entry - stores type-erased value
struct StagedWrite {
    TVarBase* tvar;
    void* value_ptr;
    void (*deleter)(void*);

    template <typename T>
    static StagedWrite create(TVar<T>* tv, T val) {
        StagedWrite sw;
        sw.tvar = tv;
        sw.value_ptr = new T(bsl::move(val));
        sw.deleter = [](void* p) { delete static_cast<T*>(p); };
        return sw;
    }

    void destroy() {
        if (deleter && value_ptr) {
            deleter(value_ptr);
            value_ptr = nullptr;
        }
    }

    void commit() {
        tvar->commit_write(value_ptr);
    }
};

// Read set entry
struct ReadEntry {
    TVarBase* tvar;
    uint64_t version;
};

// Optimized transaction using flat vectors instead of hash maps
struct Transaction {
    // Use small vectors - most transactions touch few TVars
    bsl::vector<ReadEntry> readSet;
    bsl::vector<StagedWrite> staged;
    bsl::vector<bsl::shared_ptr<TVarBase>> keepAlive;
    bool wantsRetry = false;

    Transaction() {
        readSet.reserve(16);
        staged.reserve(8);
        keepAlive.reserve(16);
    }

    void reset() {
        readSet.clear();
        for (auto& sw : staged) {
            sw.destroy();
        }
        staged.clear();
        keepAlive.clear();
        wantsRetry = false;
    }

    ~Transaction() {
        for (auto& sw : staged) {
            sw.destroy();
        }
    }

    // Find staged write for a TVar (returns nullptr if not found)
    void* find_staged(TVarBase* tv) {
        for (auto& sw : staged) {
            if (sw.tvar == tv) return sw.value_ptr;
        }
        return nullptr;
    }

    // Find or add to read set, returns pointer to version slot
    uint64_t* find_or_add_read(TVarBase* tv) {
        for (auto& re : readSet) {
            if (re.tvar == tv) return &re.version;
        }
        return nullptr;
    }

    void add_read(TVarBase* tv, uint64_t ver) {
        readSet.push_back({tv, ver});
    }

    void add_or_update_staged(StagedWrite sw) {
        for (auto& existing : staged) {
            if (existing.tvar == sw.tvar) {
                existing.destroy();
                existing = sw;
                return;
            }
        }
        staged.push_back(sw);
    }
};

inline thread_local Transaction* g_tx = nullptr;

struct TxScope {
    explicit TxScope(Transaction& t) noexcept { g_tx = &t; }
    ~TxScope() noexcept { g_tx = nullptr; }
    TxScope(const TxScope&) = delete;
    TxScope& operator=(const TxScope&) = delete;
};

namespace detail {
    inline void track_keepalive(Transaction& tx, const bsl::shared_ptr<TVarBase>& sp) {
        auto* raw = sp.get();
        for (auto const& held : tx.keepAlive) {
            if (held.get() == raw) return;
        }
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

// ---- Optimized STM API ----

template <typename T>
inline T readTVar(const bsl::shared_ptr<TVar<T>>& tv) {
    BSLS_ASSERT(g_tx && "readTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, bsl::static_pointer_cast<TVarBase>(tv));

    // Read-your-own-writes: return staged value if present
    if (void* staged = tx.find_staged(tv.get())) {
        return *static_cast<T*>(staged);
    }

    // Check if already in read set
    if (uint64_t* ver_ptr = tx.find_or_add_read(tv.get())) {
        // Already read this TVar, just return current value
        // (optimistic read - will validate at commit)
        return tv->value;
    }

    // First read: snapshot version and value atomically
    bsl::unique_lock<bsl::mutex> lk(tv->m);
    T result = tv->value;
    uint64_t ver = tv->version.load(bsl::memory_order_acquire);
    lk.unlock();

    tx.add_read(tv.get(), ver);
    return result;
}

template <typename T>
inline void writeTVar(const bsl::shared_ptr<TVar<T>>& tv, T newVal) {
    BSLS_ASSERT(g_tx && "writeTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, bsl::static_pointer_cast<TVarBase>(tv));

    // Record read version if not already tracked
    if (!tx.find_or_add_read(tv.get())) {
        bsl::unique_lock<bsl::mutex> lk(tv->m);
        uint64_t ver = tv->version.load(bsl::memory_order_acquire);
        lk.unlock();
        tx.add_read(tv.get(), ver);
    }

    // Stage the new value
    tx.add_or_update_staged(StagedWrite::create(tv.get(), bsl::move(newVal)));
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

    auto savedRead   = tx.readSet;
    auto savedKeep   = tx.keepAlive;
    // Note: staged writes are more complex to save/restore, keep simple for now

    try {
        return static_cast<R>(left());
    } catch (const TxAbortRetry&) {
        tx.readSet   = bsl::move(savedRead);
        tx.keepAlive = bsl::move(savedKeep);
        // Clear staged writes
        for (auto& sw : tx.staged) sw.destroy();
        tx.staged.clear();

        auto savedRead2 = tx.readSet;
        try {
            return static_cast<R>(right());
        } catch (const TxAbortRetry&) {
            for (auto& kv : savedRead2) {
                bool found = false;
                for (auto& re : tx.readSet) {
                    if (re.tvar == kv.tvar) { found = true; break; }
                }
                if (!found) tx.readSet.push_back(kv);
            }
            throw;
        }
    }
}

template <typename A>
auto orElse(A leftVal, A rightVal) {
    return orElse_helper([=]{ return leftVal; }, [=]{ return rightVal; });
}

// ---- Optimized atomically ----

template <typename F>
decltype(auto) atomically(F&& action) {
    using R = bsl::invoke_result_t<F&>;
    BSLS_ASSERT(g_tx == nullptr && "Nested atomically() not supported");

    Transaction tx;

    for (;;) {
        tx.reset();
        TxScope scope(tx);

        try {
            auto commit = [&] {
                // Fast path: no writes, just validate reads
                if (tx.staged.empty()) {
                    // Validate all reads without locking
                    for (auto& re : tx.readSet) {
                        uint64_t cur = re.tvar->version.load(bsl::memory_order_acquire);
                        if (cur != re.version) {
                            throw TxAbortConflict{};
                        }
                    }
                    return;
                }

                // Slow path: has writes, need to lock and validate
                // Sort writers by address to avoid deadlock
                bsl::vector<TVarBase*> writers;
                writers.reserve(tx.staged.size());
                for (auto& sw : tx.staged) {
                    writers.push_back(sw.tvar);
                }
                bsl::sort(writers.begin(), writers.end());
                writers.erase(bsl::unique(writers.begin(), writers.end()), writers.end());

                // Lock all writers
                bsl::vector<bsl::unique_lock<bsl::mutex>> held;
                held.reserve(writers.size());
                for (auto* tv : writers) {
                    held.emplace_back(tv->m);
                }

                // Validate entire read set
                for (auto& re : tx.readSet) {
                    uint64_t cur = re.tvar->version.load(bsl::memory_order_acquire);
                    if (cur != re.version) {
                        throw TxAbortConflict{};
                    }
                }

                // Commit all staged writes
                for (auto& sw : tx.staged) {
                    sw.commit();
                }
            };

            if constexpr (bsl::is_void_v<R>) {
                action();
                commit();
                return;
            } else {
                R result = action();
                commit();
                return result;
            }
        }
        catch (const TxAbortRetry&) {
            if (!tx.readSet.empty()) {
                auto& re = tx.readSet[0];
                bsl::unique_lock<bsl::mutex> lk(re.tvar->m);
                re.tvar->cv.wait(lk, [&]{
                    return re.tvar->version.load(bsl::memory_order_acquire) != re.version;
                });
            } else {
                bsl::this_thread::yield();
            }
        }
        catch (const TxAbortConflict&) {
            bsl::this_thread::yield();
        }
    }
}

} // namespace stm
