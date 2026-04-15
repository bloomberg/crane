// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// Skip List Node implementation for STM-based skip list
// This file provides the C++ runtime support for the extracted Rocq skip list.

#ifndef SKIPNODE_H
#define SKIPNODE_H

#include <memory>
#include <optional>
#include <vector>
#include <stm_adapter.h>

// Maximum levels must match SkipList.v's maxLevels
constexpr unsigned int MAX_LEVELS = 16;

/// SkipNode: a single node in the STM-based skip list.
///
/// Each node has a key, a transactional value, and a vector of forward pointers
/// (one per level).  Forward pointers are TVar<NodePtr> so that concurrent
/// transactions can safely read/write the list structure via the STM adapter.
///
/// We use std::vector<TVar<NodePtr>> rather than std::array because crane-stm's
/// TVar has no default constructor (it requires an initial value).  All
/// MAX_LEVELS entries are initialized to nullptr so that any level can be
/// accessed without bounds-checking in the extracted code.
template <typename K, typename V>
struct SkipNode {
    using NodePtr = std::shared_ptr<SkipNode<K, V>>;

    K key;
    stm::TVar<V> value;
    std::vector<stm::TVar<NodePtr>> forward;
    unsigned int level;

    SkipNode(K k, V v, unsigned int lvl)
        : key(std::move(k))
        , value(std::move(v))
        , level(lvl)
    {
        forward.reserve(MAX_LEVELS);
        for (unsigned int i = 0; i < MAX_LEVELS; ++i) {
            forward.emplace_back(stm::TVar<NodePtr>(nullptr));
        }
    }

    // Factory method that returns a shared_ptr to a new node
    static NodePtr create(K k, V v, unsigned int lvl) {
        return std::make_shared<SkipNode<K, V>>(std::move(k), std::move(v), lvl);
    }
};

// Helper functions to convert between shared_ptr and optional
template<typename T>
inline std::optional<T> ptr_to_opt(const T& ptr) {
    if (ptr) return std::optional<T>(ptr);
    return std::nullopt;
}

template<typename T>
inline T opt_to_ptr(const std::optional<T>& opt) {
    if (opt) return *opt;
    return nullptr;
}

// SkipPath: Fixed-size array for storing path predecessors at each level
// Uses shared storage so copies share the same underlying array (reference semantics)
// This is needed because the extracted code passes path by value but expects mutations to be visible
template <typename K, typename V>
struct SkipPath {
    using NodePtr = std::shared_ptr<SkipNode<K, V>>;
    using StoragePtr = std::shared_ptr<std::array<NodePtr, MAX_LEVELS>>;

    StoragePtr nodes;

    SkipPath() : nodes(std::make_shared<std::array<NodePtr, MAX_LEVELS>>()) {}

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
