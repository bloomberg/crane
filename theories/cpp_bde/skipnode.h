// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Skip List Node implementation for STM-based skip list (BDE version)
// This file provides the C++ runtime support for the extracted Rocq skip list.

#ifndef SKIPNODE_H
#define SKIPNODE_H

#include <bsl_array.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <mini_stm.h>

// Maximum levels must match SkipList.v's maxLevels
constexpr unsigned int MAX_LEVELS = 16;

template <typename K, typename V>
struct SkipNode {
    using NodePtr = bsl::shared_ptr<SkipNode<K, V>>;
    using ForwardPtr = bsl::shared_ptr<stm::TVar<NodePtr>>;

    K key;
    bsl::shared_ptr<stm::TVar<V>> value;
    // Fixed-size array avoids heap allocation for the vector
    bsl::array<ForwardPtr, MAX_LEVELS> forward;
    unsigned int level;

    SkipNode(K k, V v, unsigned int lvl)
        : key(bsl::move(k))
        , value(stm::newTVar<V>(bsl::move(v)))
        , forward{}  // Zero-initialize all pointers to nullptr
        , level(lvl)
    {
        // Create forward pointers for ALL levels (0 to MAX_LEVELS-1).
        // This is necessary because operations like removeAll may access
        // any level of a node, expecting a valid TVar (even if it points
        // to nullptr). Without this, accessing uninitialized levels would
        // dereference a null TVar pointer and crash.
        for (unsigned int i = 0; i < MAX_LEVELS; ++i) {
            forward[i] = stm::newTVar<NodePtr>(nullptr);
        }
    }

    // Factory method that returns a shared_ptr to a new node
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
