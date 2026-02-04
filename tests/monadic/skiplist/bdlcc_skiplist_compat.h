// bdlcc_skiplist_compat.h - BDE-compatible wrapper for Crane SkipList
//
// This header provides a BDE-compatible interface wrapper around the
// Crane-extracted SkipList implementation. It translates between the
// STM-based functional interface and the BDE output-parameter style.
//
// Key differences from the actual BDE implementation:
// - Uses STM for thread safety instead of mutex locks
// - Uses std::shared_ptr for reference counting instead of manual ref counting
// - "R" (reverse search) methods are not implemented; they delegate to forward search
// - KEY type must have both operator< and operator== defined
//
#ifndef INCLUDED_BDLCC_SKIPLIST_COMPAT
#define INCLUDED_BDLCC_SKIPLIST_COMPAT

#include "skiplist.h"
#include <functional>
#include <memory>
#include <optional>
#include <random>
#include <thread>
#include <utility>

namespace bdlcc_compat {

// Forward declarations
template <class KEY, class DATA>
class SkipList;

template <class KEY, class DATA>
class SkipListPairHandle;

// =============================================================================
//                            class SkipListPair
// =============================================================================

/// Opaque type representing a reference to an element in the SkipList.
/// This wraps a shared_ptr to a SkipNode, providing key() and data() accessors.
template <class KEY, class DATA>
class SkipListPair {
  private:
    std::shared_ptr<SkipNode<KEY, DATA>> d_node;

    friend class SkipList<KEY, DATA>;
    friend class SkipListPairHandle<KEY, DATA>;

    explicit SkipListPair(std::shared_ptr<SkipNode<KEY, DATA>> node)
        : d_node(std::move(node)) {}

  public:
    /// Return a reference to the modifiable "data" of this pair.
    DATA& data() const {
        return stm::readTVar<DATA>(d_node->value);
    }

    /// Return a reference to the non-modifiable "key" value of this pair.
    const KEY& key() const {
        return d_node->key;
    }

    /// Return the underlying node pointer (for internal use).
    std::shared_ptr<SkipNode<KEY, DATA>> node() const {
        return d_node;
    }
};

// =============================================================================
//                         class SkipListPairHandle
// =============================================================================

/// RAII handle for SkipList pair references. Provides automatic cleanup
/// and safe access to list elements.
template <class KEY, class DATA>
class SkipListPairHandle {
  public:
    typedef SkipListPair<KEY, DATA> Pair;

  private:
    SkipList<KEY, DATA>* d_list_p;
    std::shared_ptr<Pair> d_pair;

    friend class SkipList<KEY, DATA>;

    SkipListPairHandle(SkipList<KEY, DATA>* list, std::shared_ptr<Pair> pair)
        : d_list_p(list), d_pair(std::move(pair)) {}

  public:
    /// Construct a new PairHandle that does not refer to a pair.
    SkipListPairHandle() : d_list_p(nullptr), d_pair(nullptr) {}

    /// Copy constructor - shares ownership of the pair.
    SkipListPairHandle(const SkipListPairHandle& other) = default;

    /// Destructor - releases reference (handled by shared_ptr).
    ~SkipListPairHandle() = default;

    /// Assignment operator.
    SkipListPairHandle& operator=(const SkipListPairHandle& rhs) = default;

    /// Release the reference managed by this handle.
    void release() {
        d_pair.reset();
        d_list_p = nullptr;
    }

    /// Implicit conversion to const Pair*.
    operator const Pair*() const {
        return d_pair.get();
    }

    /// Return a reference to the "data" value of the pair.
    DATA& data() const {
        return d_pair->data();
    }

    /// Return a reference to the non-modifiable "key" value of the pair.
    const KEY& key() const {
        return d_pair->key();
    }

    /// Return true if this handle refers to a valid pair.
    bool isValid() const {
        return d_pair != nullptr;
    }
};

// =============================================================================
//                              class SkipList
// =============================================================================

/// BDE-compatible wrapper around Crane's SkipList implementation.
/// Provides the same interface as bdlcc::SkipList with output parameters
/// and integer return codes.
template <class KEY, class DATA>
class SkipList {
  public:
    // CONSTANTS
    enum {
        e_SUCCESS   = 0,
        e_NOT_FOUND = 1,
        e_DUPLICATE = 2,
        e_INVALID   = 3
    };

    // TYPES
    typedef SkipListPair<KEY, DATA>       Pair;
    typedef SkipListPairHandle<KEY, DATA> PairHandle;

  private:
    std::shared_ptr<::SkipList<KEY, DATA>> d_impl;

    // Comparison functions for KEY type
    static bool keyLt(const KEY& a, const KEY& b) { return a < b; }
    static bool keyEq(const KEY& a, const KEY& b) { return a == b; }

    // Helper to wrap a node as a Pair
    static std::shared_ptr<Pair> wrapNode(std::shared_ptr<SkipNode<KEY, DATA>> node) {
        if (!node) return nullptr;
        return std::shared_ptr<Pair>(new Pair(std::move(node)));
    }

    // Helper to run STM operation atomically
    template <typename F>
    static auto atomic(F&& f) {
        return stm::atomically(std::forward<F>(f));
    }

  public:
    // CREATORS

    /// Create a new empty SkipList.
    SkipList() {
        d_impl = atomic([] {
            return ::SkipList<int, int>::template create<KEY, DATA>(KEY{}, DATA{});
        });
    }

    /// Destroy this SkipList.
    ~SkipList() = default;

    // MANIPULATORS - Insertion Methods

    /// Add the key/data pair to this list.
    void add(const KEY& key, const DATA& data, bool* newFrontFlag = nullptr) {
        atomic([&] {
            unsigned int level = randomLevel();
            auto result = d_impl->bde_add(keyLt, keyEq, key, data, level);
            if (newFrontFlag) {
                *newFrontFlag = result.second;
            }
        });
    }

    /// Add the key/data pair and load result into the PairHandle.
    void add(PairHandle* result, const KEY& key, const DATA& data,
             bool* newFrontFlag = nullptr) {
        atomic([&] {
            unsigned int level = randomLevel();
            auto addResult = d_impl->bde_add(keyLt, keyEq, key, data, level);
            if (result) {
                *result = PairHandle(this, wrapNode(addResult.first));
            }
            if (newFrontFlag) {
                *newFrontFlag = addResult.second;
            }
        });
    }

    /// Add the key/data pair only if key is not already present.
    /// Return 0 on success, e_DUPLICATE if key exists.
    int addUnique(const KEY& key, const DATA& data, bool* newFrontFlag = nullptr) {
        return atomic([&]() -> int {
            unsigned int level = randomLevel();
            auto result = d_impl->bde_addUnique(keyLt, keyEq, key, data, level);
            auto status = result.first.first;
            if (newFrontFlag && status == e_SUCCESS) {
                *newFrontFlag = result.second;
            }
            return (status == e_DUPLICATE) ? e_DUPLICATE : e_SUCCESS;
        });
    }

    /// Add the key/data pair only if key is not already present.
    /// Load result into PairHandle. Return 0 on success.
    int addUnique(PairHandle* result, const KEY& key, const DATA& data,
                  bool* newFrontFlag = nullptr) {
        return atomic([&]() -> int {
            unsigned int level = randomLevel();
            auto addResult = d_impl->bde_addUnique(keyLt, keyEq, key, data, level);
            auto status = addResult.first.first;
            if (status == e_SUCCESS && result && addResult.first.second.has_value()) {
                *result = PairHandle(this, wrapNode(*addResult.first.second));
            }
            if (newFrontFlag && status == e_SUCCESS) {
                *newFrontFlag = addResult.second;
            }
            return (status == e_DUPLICATE) ? e_DUPLICATE : e_SUCCESS;
        });
    }

    // Reverse search variants (delegate to forward search - "R" optimization not implemented)
    void addR(const KEY& key, const DATA& data, bool* newFrontFlag = nullptr) {
        add(key, data, newFrontFlag);
    }

    void addR(PairHandle* result, const KEY& key, const DATA& data,
              bool* newFrontFlag = nullptr) {
        add(result, key, data, newFrontFlag);
    }

    int addUniqueR(const KEY& key, const DATA& data, bool* newFrontFlag = nullptr) {
        return addUnique(key, data, newFrontFlag);
    }

    int addUniqueR(PairHandle* result, const KEY& key, const DATA& data,
                   bool* newFrontFlag = nullptr) {
        return addUnique(result, key, data, newFrontFlag);
    }

    // MANIPULATORS - Removal Methods

    /// Remove the first item from the list.
    /// Return 0 on success, non-zero if list is empty.
    int popFront(PairHandle* item = nullptr) {
        return atomic([&]() -> int {
            auto result = d_impl->bde_popFront();
            if (result.first == e_SUCCESS && item && result.second.has_value()) {
                *item = PairHandle(this, wrapNode(*result.second));
            }
            return result.first;
        });
    }

    /// Remove the item identified by the pair.
    /// Return 0 on success, e_NOT_FOUND if not in list.
    int remove(const Pair* reference) {
        if (!reference) return e_NOT_FOUND;
        return atomic([&]() -> int {
            return d_impl->bde_remove(keyLt, keyEq, reference->node());
        });
    }

    /// Remove all items from this list.
    /// Return the number of items removed.
    int removeAll() {
        return atomic([&]() -> int {
            return static_cast<int>(d_impl->bde_removeAll());
        });
    }

    // ACCESSORS

    /// Load a reference to the last item into back.
    /// Return 0 on success, non-zero if list is empty.
    int back(PairHandle* back) const {
        return atomic([&]() -> int {
            auto result = d_impl->bde_back();
            if (result.first == e_SUCCESS && back && result.second.has_value()) {
                *back = PairHandle(const_cast<SkipList*>(this), wrapNode(*result.second));
            }
            return result.first;
        });
    }

    /// Return true if there is a pair with the specified key.
    bool exists(const KEY& key) const {
        return atomic([&]() -> bool {
            return d_impl->bde_exists(keyLt, keyEq, key);
        });
    }

    /// Load a reference to the first item into front.
    /// Return 0 on success, non-zero if list is empty.
    int front(PairHandle* front) const {
        return atomic([&]() -> int {
            auto result = d_impl->bde_front();
            if (result.first == e_SUCCESS && front && result.second.has_value()) {
                *front = PairHandle(const_cast<SkipList*>(this), wrapNode(*result.second));
            }
            return result.first;
        });
    }

    /// Return true if this list is empty.
    bool isEmpty() const {
        return atomic([&]() -> bool {
            return d_impl->bde_isEmpty();
        });
    }

    /// Return the number of items in this list.
    int length() const {
        return atomic([&]() -> int {
            return static_cast<int>(d_impl->bde_length());
        });
    }

    // Find Methods

    /// Find element with the specified key.
    /// Return 0 on success, non-zero if not found.
    int find(PairHandle* item, const KEY& key) const {
        return atomic([&]() -> int {
            auto result = d_impl->bde_find(keyLt, keyEq, key);
            if (result.first == e_SUCCESS && item && result.second.has_value()) {
                *item = PairHandle(const_cast<SkipList*>(this), wrapNode(*result.second));
            }
            return result.first;
        });
    }

    /// Reverse search variant (delegates to forward search).
    int findR(PairHandle* item, const KEY& key) const {
        return find(item, key);
    }

    /// Find first element whose key is not less than the specified key.
    int findLowerBound(PairHandle* item, const KEY& key) const {
        return atomic([&]() -> int {
            auto result = d_impl->bde_findLowerBound(keyLt, key);
            if (result.first == e_SUCCESS && item && result.second.has_value()) {
                *item = PairHandle(const_cast<SkipList*>(this), wrapNode(*result.second));
            }
            return result.first;
        });
    }

    int findLowerBoundR(PairHandle* item, const KEY& key) const {
        return findLowerBound(item, key);
    }

    /// Find first element whose key is greater than the specified key.
    int findUpperBound(PairHandle* item, const KEY& key) const {
        return atomic([&]() -> int {
            auto result = d_impl->bde_findUpperBound(keyLt, keyEq, key);
            if (result.first == e_SUCCESS && item && result.second.has_value()) {
                *item = PairHandle(const_cast<SkipList*>(this), wrapNode(*result.second));
            }
            return result.first;
        });
    }

    int findUpperBoundR(PairHandle* item, const KEY& key) const {
        return findUpperBound(item, key);
    }

    // Navigation Methods

    /// Load into next a reference to the item after reference.
    /// Return 0 on success, non-zero if reference is at back.
    int next(PairHandle* next, const Pair* reference) const {
        if (!reference) return e_NOT_FOUND;
        return atomic([&]() -> int {
            auto result = ::SkipList<int, int>::template bde_next<KEY, DATA>(reference->node());
            if (result.first == e_SUCCESS && next && result.second.has_value()) {
                *next = PairHandle(const_cast<SkipList*>(this), wrapNode(*result.second));
            }
            return result.first;
        });
    }

    /// Load into prevPair a reference to the item before reference.
    /// Return 0 on success, non-zero if reference is at front.
    int previous(PairHandle* prevPair, const Pair* reference) const {
        if (!reference) return e_NOT_FOUND;
        return atomic([&]() -> int {
            auto result = d_impl->bde_previous(keyEq, reference->node());
            if (result.first == e_SUCCESS && prevPair && result.second.has_value()) {
                *prevPair = PairHandle(const_cast<SkipList*>(this), wrapNode(*result.second));
            }
            return result.first;
        });
    }

    /// If item is not at front, load the previous item into item; otherwise reset.
    /// Return 0 on success, e_NOT_FOUND if item is no longer in list.
    int skipBackward(PairHandle* item) const {
        if (!item || !item->isValid()) return e_NOT_FOUND;
        PairHandle prev;
        int rc = previous(&prev, static_cast<const Pair*>(*item));
        if (rc == e_SUCCESS) {
            *item = prev;
        } else {
            item->release();
        }
        return e_SUCCESS;
    }

    /// If item is not at back, load the next item into item; otherwise reset.
    /// Return 0 on success, e_NOT_FOUND if item is no longer in list.
    int skipForward(PairHandle* item) const {
        if (!item || !item->isValid()) return e_NOT_FOUND;
        PairHandle nextItem;
        int rc = next(&nextItem, static_cast<const Pair*>(*item));
        if (rc == e_SUCCESS) {
            *item = nextItem;
        } else {
            item->release();
        }
        return e_SUCCESS;
    }

  private:
    // Generate a random level for new nodes
    static unsigned int randomLevel() {
        // Use thread-local RNG for thread safety
        // Seed with a hash of thread ID for deterministic but varied seeds
        thread_local std::mt19937 rng(
            static_cast<unsigned>(std::hash<std::thread::id>{}(std::this_thread::get_id()))
        );
        unsigned int level = 0;
        while ((rng() & 1) && level < 15) {
            ++level;
        }
        return level;
    }
};

} // namespace bdlcc_compat

#endif // INCLUDED_BDLCC_SKIPLIST_COMPAT
