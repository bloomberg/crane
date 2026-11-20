// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// C++ side of the typed_mapping_access test: a mutable cell behind a
// shared_ptr handle, and a mutable buffer value.
#pragma once

#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

namespace access_support {

struct cell {
  std::int64_t value;
};

using handle = std::shared_ptr<cell>;

inline handle make(std::uint64_t n) {
  return std::make_shared<cell>(cell{static_cast<std::int64_t>(n)});
}

inline std::uint64_t get(const handle &h) {
  return static_cast<std::uint64_t>(h->value);
}

// Writes through the handle: the referent changes, the handle does not.
inline handle set(const handle &h, std::uint64_t n) {
  h->value = static_cast<std::int64_t>(n);
  return h;
}

// Reseats the caller's handle on a fresh cell.
inline handle reseat(handle &h, std::uint64_t n) {
  h = make(n);
  return h;
}

// Keeps the handle it is given.
inline handle keep(handle h) { return h; }

struct buf {
  std::vector<std::uint64_t> items;
};

inline buf buf_make(std::uint64_t n) { return buf{std::vector<std::uint64_t>(n, 0)}; }

inline std::uint64_t buf_len(const buf &b) { return b.items.size(); }

// Writes the buffer in place.
inline buf buf_push(buf &b, std::uint64_t x) {
  b.items.push_back(x);
  return b;
}

} // namespace access_support
