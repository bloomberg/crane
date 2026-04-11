// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// persistent_array.h — Copy-on-Write persistent array for Crane extraction
//
// Rocq's PrimArray is a persistent data structure: `set` returns a new array
// and leaves the original unchanged. This C++ implementation preserves those
// semantics using a shared_ptr<vector> with copy-on-write (COW).
//
// Persistence guarantee:
//   - set() returns a new persistent_array by value.
//   - The original array is never mutated through the public interface.
//
// COW optimization via ref-qualified overloads:
//   - set(...) const &  — called on lvalues (named variables). ALWAYS deep-
//     copies the vector to guarantee the original is unchanged. This is the
//     safe path that preserves persistent semantics.
//   - set(...) &&       — called on rvalues (temporaries, e.g. chained sets
//     like arr.set(0,x).set(1,y).set(2,z)). When the vector has a single
//     owner (use_count() == 1), it mutates in-place — O(1). This is safe
//     because the temporary is about to be destroyed; no one can observe the
//     mutation through the old handle.
//
//   Crane's escape analysis (PR #22) determines unique ownership at the Rocq
//   level. When Crane generates a = set(a, i, v) (rebinding `a`), the old
//   value becomes a temporary and the && overload fires automatically.
//
// Why not immer::flex_vector?
//   - COW is correct, simple, has no external dependencies, and gives O(1)
//     set for the common case (chained/linear use).
//   - If profiling shows O(n) copies are a bottleneck for heavily-branching
//     array usage, immer is a drop-in replacement — same interface, O(log n)
//     persistent set. The extraction directives don't change; only this header
//     would be swapped out.
//
// Index type:
//   All indices are int64_t, matching Crane's int63 extraction (PR #44).

#pragma once
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

template<typename T>
class persistent_array {
    std::shared_ptr<std::vector<T>> data_;
    T default_;

public:
    // Construct an array of `len` elements, each initialized to `def`.
    // Matches PrimArray.make.
    persistent_array(int64_t len, T def)
        : data_(std::make_shared<std::vector<T>>(len, def))
        , default_(std::move(def))
    {}

    // Read element at index `i`. Returns default_ on out-of-bounds.
    // Matches PrimArray.get (which returns the array's default on OOB).
    T get(int64_t i) const {
        if (i >= 0 && i < static_cast<int64_t>(data_->size()))
            return (*data_)[static_cast<size_t>(i)];
        return default_;
    }

    // Lvalue overload: called on named variables (e.g. arr.set(i, v) where
    // arr is a persistent_array that the caller keeps using afterward).
    // Always deep-copies to preserve the original — this is the core
    // persistence guarantee.
    persistent_array set(int64_t i, T val) const & {
        if (i < 0 || i >= static_cast<int64_t>(data_->size()))
            return *this;  // OOB set is a no-op in Rocq

        // Always deep-copy: the caller still holds `this`, so we must not
        // mutate the shared vector.
        auto new_data = std::make_shared<std::vector<T>>(*data_);
        (*new_data)[static_cast<size_t>(i)] = std::move(val);
        persistent_array result;
        result.data_ = std::move(new_data);
        result.default_ = default_;
        return result;
    }

    // Rvalue overload: called on temporaries (e.g. arr.set(0,x).set(1,y) —
    // the intermediate results are temporaries that no one else can observe).
    // When we are the sole owner, we can mutate in-place — O(1).
    persistent_array set(int64_t i, T val) && {
        if (i < 0 || i >= static_cast<int64_t>(data_->size()))
            return std::move(*this);

        if (data_.use_count() == 1) {
            // Sole owner of a temporary — safe to mutate in-place.
            (*data_)[static_cast<size_t>(i)] = std::move(val);
            return std::move(*this);
        }

        // Shared even though we're a temporary (rare). Deep-copy.
        auto new_data = std::make_shared<std::vector<T>>(*data_);
        (*new_data)[static_cast<size_t>(i)] = std::move(val);
        persistent_array result;
        result.data_ = std::move(new_data);
        result.default_ = default_;
        return result;
    }

    // Number of elements. Matches PrimArray.length.
    int64_t length() const {
        return static_cast<int64_t>(data_->size());
    }

    // Independent deep copy. Matches PrimArray.copy.
    persistent_array copy() const {
        persistent_array result;
        result.data_ = std::make_shared<std::vector<T>>(*data_);
        result.default_ = default_;
        return result;
    }

private:
    // Default constructor for internal use (set/copy factory).
    persistent_array() : default_{} {}
};
