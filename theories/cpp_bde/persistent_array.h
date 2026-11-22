// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// persistent_array.h — Copy-on-Write persistent array for Crane extraction
//                      (BDE edition)
//
// This is the BDE counterpart of theories/cpp/persistent_array.h, using
// bsl:: types (bsl::shared_ptr, bsl::vector, bsl::move) instead of std::.
// See the std version for design rationale (COW, ref-qualified overloads,
// escape analysis, immer alternative).

#pragma once
#include <bsl_cstdint.h>
#include <bsl_memory.h>
#include <bsl_utility.h>
#include <bsl_vector.h>

using namespace BloombergLP;

template<typename T>
class persistent_array {
    bsl::shared_ptr<bsl::vector<T>> data_;
    T default_;

    // An array holding `data`, with `def` for its out-of-bounds reads.
    persistent_array(bsl::shared_ptr<bsl::vector<T>> data, T def)
        : data_(bsl::move(data)), default_(bsl::move(def)) {}

public:
    // PrimArray.max_length: the longest array Rocq's make builds.
    static constexpr int64_t max_length = 4194303;

    // Construct an array of `len` elements, each initialized to `def`.
    // Matches PrimArray.make, which clamps `len` to max_length.
    persistent_array(int64_t len, T def)
        : data_(bsl::make_shared<bsl::vector<T>>(
              static_cast<typename bsl::vector<T>::size_type>(
                  len < max_length ? len : max_length), def))
        , default_(bsl::move(def))
    {}

    // The empty array, its default element value-initialised.  Rocq never
    // builds one; a holder does where it default-constructs its members --
    // an array of arrays keeping its default element, a variant whose first
    // alternative holds an array, a local declared ahead of the branches
    // that assign it.
    persistent_array() : persistent_array(bsl::make_shared<bsl::vector<T>>(), T{}) {}

    // The element out-of-bounds reads give. Matches PrimArray.default.
    T default_value() const { return default_; }

    // Read element at index `i`. Returns default_ on out-of-bounds.
    // Matches PrimArray.get (which returns the array's default on OOB).
    T get(int64_t i) const {
        if (i >= 0 && i < static_cast<int64_t>(data_->size()))
            return (*data_)[i];
        return default_;
    }

    // Lvalue overload: called on named variables. Always deep-copies to
    // preserve the original — this is the core persistence guarantee.
    persistent_array set(int64_t i, T val) const & {
        if (i < 0 || i >= static_cast<int64_t>(data_->size()))
            return *this;

        auto new_data = bsl::make_shared<bsl::vector<T>>(*data_);
        (*new_data)[i] = bsl::move(val);
        return persistent_array(bsl::move(new_data), default_);
    }

    // Rvalue overload: called on temporaries (chained sets). When we are
    // the sole owner, mutate in-place — O(1).
    persistent_array set(int64_t i, T val) && {
        if (i < 0 || i >= static_cast<int64_t>(data_->size()))
            return bsl::move(*this);

        if (data_.use_count() == 1) {
            (*data_)[i] = bsl::move(val);
            return bsl::move(*this);
        }

        auto new_data = bsl::make_shared<bsl::vector<T>>(*data_);
        (*new_data)[i] = bsl::move(val);
        return persistent_array(bsl::move(new_data), default_);
    }

    // Number of elements. Matches PrimArray.length.
    int64_t length() const {
        return static_cast<int64_t>(data_->size());
    }

    // Independent deep copy. Matches PrimArray.copy.
    persistent_array copy() const {
        return persistent_array(bsl::make_shared<bsl::vector<T>>(*data_), default_);
    }
};
