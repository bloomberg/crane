#pragma once

#include <atomic>
#include <condition_variable>
#include <cstdint>
#include <functional>
#include <mutex>
#include <thread>
#include <type_traits>
#include <utility>
#include <vector>
#include <algorithm>
#include <memory>
#include <concepts>
#include <cassert>

namespace stm {

struct TVarBase;
struct TxAbortRetry final {};
struct TxAbortConflict final {};

template <typename FLeft, typename FRight>
concept SameReturn = std::invocable<FLeft&> && std::invocable<FRight&> &&
                     std::same_as<std::invoke_result_t<FLeft&>, std::invoke_result_t<FRight&>>;

struct TVarBase : public std::enable_shared_from_this<TVarBase> {
    std::atomic<uint64_t> version{0};
    mutable std::mutex m;
    std::condition_variable cv;
    virtual ~TVarBase() = default;
    virtual void commit_write(void* staged_ptr) = 0;
};

template <typename T>
struct TVar : TVarBase {
    static_assert(std::is_nothrow_move_constructible_v<T>,
                  "T must be nothrow move constructible for STM commit strong exception safety");
    static_assert(std::is_nothrow_swappable_v<T>,
                  "T must be nothrow swappable for STM commit strong exception safety");

    T value;

    explicit TVar(T v) : value(std::move(v)) {}

    void commit_write(void* staged_ptr) override {
        T* staged = static_cast<T*>(staged_ptr);
        using std::swap;
        swap(value, *staged);
        version.fetch_add(1, std::memory_order_release);
        cv.notify_all();
    }

    // Lock-free read of current value (caller handles validation)
    T read_value() const {
        return value;
    }

    // STM-aware read - defined after Transaction is declared
    inline T read() const;

    // STM-aware write - defined after Transaction is declared
    inline void write(T newVal);
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
        sw.value_ptr = new T(std::move(val));
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
    std::vector<ReadEntry> readSet;
    std::vector<StagedWrite> staged;
    std::vector<std::shared_ptr<TVarBase>> keepAlive;
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
    inline void track_keepalive(Transaction& tx, const std::shared_ptr<TVarBase>& sp) {
        auto* raw = sp.get();
        for (auto const& held : tx.keepAlive) {
            if (held.get() == raw) return;
        }
        tx.keepAlive.push_back(sp);
    }
}

// ---- TVar member function definitions (for better inlining) ----

template <typename T>
inline T TVar<T>::read() const {
    assert(g_tx && "read() must be called inside atomically()");
    Transaction& tx = *g_tx;
    auto self = std::const_pointer_cast<TVarBase>(shared_from_this());
    detail::track_keepalive(tx, self);

    // Read-your-own-writes: return staged value if present
    if (void* staged = tx.find_staged(self.get())) {
        return *static_cast<T*>(staged);
    }

    // Check if already in read set
    if (tx.find_or_add_read(self.get())) {
        // Already read this TVar, just return current value
        // (optimistic read - will validate at commit)
        return value;
    }

    // First read: snapshot version and value atomically
    std::unique_lock<std::mutex> lk(m);
    T result = value;
    uint64_t ver = version.load(std::memory_order_acquire);
    lk.unlock();

    tx.add_read(self.get(), ver);
    return result;
}

template <typename T>
inline void TVar<T>::write(T newVal) {
    assert(g_tx && "write() must be called inside atomically()");
    Transaction& tx = *g_tx;
    auto self = std::const_pointer_cast<TVarBase>(shared_from_this());
    detail::track_keepalive(tx, self);

    // Record read version if not already tracked
    if (!tx.find_or_add_read(self.get())) {
        std::unique_lock<std::mutex> lk(m);
        uint64_t ver = version.load(std::memory_order_acquire);
        lk.unlock();
        tx.add_read(self.get(), ver);
    }

    // Stage the new value
    tx.add_or_update_staged(StagedWrite::create(static_cast<TVar<T>*>(self.get()), std::move(newVal)));
}

template <typename T>
inline std::shared_ptr<TVar<T>> newTVar(T init) {
    return std::make_shared<TVar<T>>(std::move(init));
}

template <typename T>
inline T readTVarIO(const TVar<T>& tv) {
    std::lock_guard<std::mutex> lk(tv.m);
    return tv.value;
}

// ---- Optimized STM API ----

template <typename T>
inline T readTVar(const std::shared_ptr<TVar<T>>& tv) {
    assert(g_tx && "readTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, std::static_pointer_cast<TVarBase>(tv));

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
    std::unique_lock<std::mutex> lk(tv->m);
    T result = tv->value;
    uint64_t ver = tv->version.load(std::memory_order_acquire);
    lk.unlock();

    tx.add_read(tv.get(), ver);
    return result;
}

template <typename T>
inline void writeTVar(const std::shared_ptr<TVar<T>>& tv, T newVal) {
    assert(g_tx && "writeTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, std::static_pointer_cast<TVarBase>(tv));

    // Record read version if not already tracked
    if (!tx.find_or_add_read(tv.get())) {
        std::unique_lock<std::mutex> lk(tv->m);
        uint64_t ver = tv->version.load(std::memory_order_acquire);
        lk.unlock();
        tx.add_read(tv.get(), ver);
    }

    // Stage the new value
    tx.add_or_update_staged(StagedWrite::create(tv.get(), std::move(newVal)));
}

// ---- retry / orElse ----

template <typename T>
[[noreturn]] inline T retry() {
    assert(g_tx && "retry() must be called inside atomically()");
    g_tx->wantsRetry = true;
    throw TxAbortRetry{};
}

template <typename FLeft, typename FRight>
requires SameReturn<FLeft, FRight>
auto orElse_helper(FLeft&& left, FRight&& right) -> std::invoke_result_t<FLeft&> {
    using R = std::invoke_result_t<FLeft&>;
    assert(g_tx && "orElse must be called inside atomically()");
    Transaction& tx = *g_tx;

    auto savedRead   = tx.readSet;
    auto savedKeep   = tx.keepAlive;
    // Note: staged writes are more complex to save/restore, keep simple for now

    try {
        return static_cast<R>(left());
    } catch (const TxAbortRetry&) {
        tx.readSet   = std::move(savedRead);
        tx.keepAlive = std::move(savedKeep);
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
    using R = std::invoke_result_t<F&>;
    assert(g_tx == nullptr && "Nested atomically() not supported");

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
                        uint64_t cur = re.tvar->version.load(std::memory_order_acquire);
                        if (cur != re.version) {
                            throw TxAbortConflict{};
                        }
                    }
                    return;
                }

                // Slow path: has writes, need to lock and validate
                // Sort writers by address to avoid deadlock
                std::vector<TVarBase*> writers;
                writers.reserve(tx.staged.size());
                for (auto& sw : tx.staged) {
                    writers.push_back(sw.tvar);
                }
                std::sort(writers.begin(), writers.end());
                writers.erase(std::unique(writers.begin(), writers.end()), writers.end());

                // Lock all writers
                std::vector<std::unique_lock<std::mutex>> held;
                held.reserve(writers.size());
                for (auto* tv : writers) {
                    held.emplace_back(tv->m);
                }

                // Validate entire read set
                for (auto& re : tx.readSet) {
                    uint64_t cur = re.tvar->version.load(std::memory_order_acquire);
                    if (cur != re.version) {
                        throw TxAbortConflict{};
                    }
                }

                // Commit all staged writes
                for (auto& sw : tx.staged) {
                    sw.commit();
                }
            };

            if constexpr (std::is_void_v<R>) {
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
                std::unique_lock<std::mutex> lk(re.tvar->m);
                re.tvar->cv.wait(lk, [&]{
                    return re.tvar->version.load(std::memory_order_acquire) != re.version;
                });
            } else {
                std::this_thread::yield();
            }
        }
        catch (const TxAbortConflict&) {
            std::this_thread::yield();
        }
    }
}

} // namespace stm
