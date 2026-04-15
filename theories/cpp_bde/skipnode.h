// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Skip List Node implementation for STM-based skip list (BDE version)
// This file provides the C++ runtime support for the extracted Rocq skip list.

#ifndef SKIPNODE_H
#define SKIPNODE_H

#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_vector.h>
#include <stm_adapter.h>

// Maximum levels must match SkipList.v's maxLevels
constexpr unsigned int MAX_LEVELS = 16;

/// SkipNode: a single node in the STM-based skip list (BDE flavor).
///
/// Each node stores a key, a transactional value, and a vector of forward
/// pointers (one per level, up to MAX_LEVELS).  All forward pointers are
/// stm::TVar<NodePtr> so concurrent transactions can read/write the list
/// structure safely through the STM adapter.
///
/// bsl::vector is used instead of bsl::array because crane-stm's TVar
/// requires an initial value and has no default constructor.  All MAX_LEVELS
/// entries are pre-initialized to nullptr so extracted code can access any
/// level without bounds-checking.
template <typename K, typename V>
struct SkipNode {
    using NodePtr = bsl::shared_ptr<SkipNode<K, V>>;

    K key;
    stm::TVar<V> value;
    bsl::vector<stm::TVar<NodePtr>> forward;
    unsigned int level;

    SkipNode(K k, V v, unsigned int lvl)
        : key(bsl::move(k))
        , value(bsl::move(v))
        , level(lvl)
    {
        forward.reserve(MAX_LEVELS);
        for (unsigned int i = 0; i < MAX_LEVELS; ++i) {
            forward.emplace_back(stm::TVar<NodePtr>(nullptr));
        }
    }

    /// Factory: returns a heap-allocated node wrapped in bsl::shared_ptr.
    static NodePtr create(K k, V v, unsigned int lvl) {
        return bsl::make_shared<SkipNode<K, V>>(bsl::move(k), bsl::move(v), lvl);
    }
};

// Helper functions to convert between shared_ptr and optional
template<typename T>
inline bsl::optional<T> ptr_to_opt(const T& ptr) {
    if (ptr) return bsl::optional<T>(ptr);
    return bsl::nullopt;
}

template<typename T>
inline T opt_to_ptr(const bsl::optional<T>& opt) {
    if (opt) return *opt;
    return nullptr;
}

// SkipPath: Fixed-size array for storing path predecessors at each level
// Uses shared storage so copies share the same underlying array (reference semantics)
// This is needed because the extracted code passes path by value but expects mutations to be visible
template <typename K, typename V>
struct SkipPath {
    using NodePtr = bsl::shared_ptr<SkipNode<K, V>>;
    using StoragePtr = bsl::shared_ptr<bsl::array<NodePtr, MAX_LEVELS>>;

    StoragePtr nodes;

    SkipPath() : nodes(bsl::make_shared<bsl::array<NodePtr, MAX_LEVELS>>()) {}

    void set(unsigned int level, const NodePtr& node) const {
        if (level < MAX_LEVELS) {
            (*nodes)[level] = node;
        }
    }

    NodePtr get(unsigned int level) const {
        if (level < MAX_LEVELS) {
            return (*nodes)[level];
        }
        return nullptr;
    }
};

#endif // SKIPNODE_H
