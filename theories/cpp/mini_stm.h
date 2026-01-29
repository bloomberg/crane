#pragma once

#include <atomic>
#include <condition_variable>
#include <cstdint>
#include <functional>
#include <mutex>
#include <thread>
#include <type_traits>
#include <unordered_map>
#include <utility>
#include <vector>
#include <algorithm>
#include <memory>
#include <concepts>
#include <cassert> // NEW: for asserts

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
    virtual void publish_boxed(std::shared_ptr<void> boxed) = 0;
};

template <typename T>
struct TVar : TVarBase {
    // Strong exception-safety for commit:
    // Require nothrow move + nothrow swap so publish_boxed can't break atomicity.
    static_assert(std::is_nothrow_move_constructible_v<T>,
                  "T must be nothrow move constructible for STM commit strong exception safety");
    static_assert(std::is_nothrow_swappable_v<T>,
                  "T must be nothrow swappable for STM commit strong exception safety");

    T value;

    explicit TVar(T v) : value(std::move(v)) {}

    void publish_boxed(std::shared_ptr<void> boxed) override {
        // Called with tv.m held by the caller.
        T tmp = std::move(*static_cast<T*>(boxed.get())); // assumes nothrow move-constructible
        using std::swap;
        swap(value, tmp); // assumes nothrow swappable
        version.fetch_add(1, std::memory_order_release);
        cv.notify_all();
    }
};

struct Transaction {
    std::unordered_map<TVarBase*, uint64_t> readSet;
    std::unordered_map<TVarBase*, std::shared_ptr<void>> staged;
    std::vector<std::shared_ptr<TVarBase>> keepAlive;
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
    inline std::shared_ptr<void> box(T&& v) {
        return std::shared_ptr<void>(new std::decay_t<T>(std::forward<T>(v)),
                                     [](void* p){ delete static_cast<std::decay_t<T>*>(p); });
    }
    template <class T>
    inline T& unbox_ref(const std::shared_ptr<void>& p) {
        return *static_cast<T*>(p.get());
    }
    inline void track_keepalive(Transaction& tx, const std::shared_ptr<TVarBase>& sp) {
        auto* raw = sp.get();
        for (auto const& held : tx.keepAlive) if (held.get() == raw) return;
        tx.keepAlive.push_back(sp);
    }
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

// ---- STM API ONLY via shared_ptr to avoid shared_from_this() UB on stack TVars ----

template <typename T>
inline T readTVar(const std::shared_ptr<TVar<T>>& tv) {
    assert(g_tx && "readTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, std::static_pointer_cast<TVarBase>(tv));

    // Read-your-own-writes: return staged value if present
    if (auto it = tx.staged.find(tv.get()); it != tx.staged.end()) {
        return detail::unbox_ref<T>(it->second);
    }

    // Coherent read under lock; record version while holding lock
    std::unique_lock<std::mutex> lk(tv->m);
    T result = tv->value; // copy
    uint64_t ver = tv->version.load(std::memory_order_acquire);
    tx.readSet.emplace(tv.get(), ver);
    return result;
}

template <typename T>
inline void writeTVar(const std::shared_ptr<TVar<T>>& tv, T newVal) {
    assert(g_tx && "writeTVar must be called inside atomically()");
    Transaction& tx = *g_tx;
    detail::track_keepalive(tx, std::static_pointer_cast<TVarBase>(tv));

    // On first touch of this TVar, record its current version in the read-set
    if (tx.readSet.find(tv.get()) == tx.readSet.end()) {
        std::unique_lock<std::mutex> lk(tv->m);
        uint64_t ver = tv->version.load(std::memory_order_acquire);
        tx.readSet.emplace(tv.get(), ver);
    }

    // Stage the new value (overwrites previous staging if any)
    tx.staged[tv.get()] = detail::box(std::move(newVal));
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

    auto savedRead     = tx.readSet;
    auto savedStaged   = tx.staged;
    auto savedKeep     = tx.keepAlive;

    try {
        return static_cast<R>(left());
    } catch (const TxAbortRetry&) {
        tx.readSet   = std::move(savedRead);
        tx.staged    = std::move(savedStaged);
        tx.keepAlive = std::move(savedKeep);

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
    using R = std::invoke_result_t<F&>;
    // Forbid nested transactions with a single g_tx pointer.
    assert(g_tx == nullptr && "Nested atomically() not supported");

    Transaction tx;

    for (;;) {
        tx.reset();
        TxScope scope(tx); // RAII: sets g_tx, clears on scope exit

        try {
            // Commit routine shared by both branches.
            auto commit = [&] {
                // Determine writer set and lock in a total order to avoid deadlocks
                std::vector<TVarBase*> writers;
                writers.reserve(tx.staged.size());
                for (auto& kv : tx.staged) writers.push_back(kv.first);
                std::sort(writers.begin(), writers.end());
                writers.erase(std::unique(writers.begin(), writers.end()), writers.end());

                std::vector<std::unique_lock<std::mutex>> held;
                held.reserve(writers.size());
                for (auto* tv : writers) held.emplace_back(tv->m);

                // Validate read set (writers are locked; non-writers can change and will cause abort)
                for (auto& kv : tx.readSet) {
                    TVarBase* tv = kv.first;
                    uint64_t seen = kv.second;
                    uint64_t cur = tv->version.load(std::memory_order_acquire);
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

            if constexpr (std::is_void_v<R>) {
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
                std::unique_lock<std::mutex> lk(tv->m);
                tv->cv.wait(lk, [&]{ return tv->version.load(std::memory_order_acquire) != seen; });
            } else {
                // No reads; just yield to avoid hot-spinning forever
                std::this_thread::yield();
            }
            // loop and retry
        }
        catch (const TxAbortConflict&) {
            // Simple backoff to reduce livelock risk
            std::this_thread::yield();
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

// std::function<R()>
template <typename T>
inline T atomically(const std::function<T()>& f) {
    return atomically([&]{ return f(); });
}
*/

} // namespace stm
