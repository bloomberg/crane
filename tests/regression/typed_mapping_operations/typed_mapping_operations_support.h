// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// C++ side of the typed_mapping_operations test: a log of effects, a
// copy-counting buffer and a mutable cell.
#pragma once

#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

namespace ops_support {

// Every value tick or log_counter saw, in order.
inline std::vector<std::uint64_t> &trace() {
  static std::vector<std::uint64_t> t;
  return t;
}

// An effect on an argument: records it, returns it.
inline std::uint64_t tick(std::uint64_t n) {
  trace().push_back(n);
  return n;
}

inline std::int64_t log_counter(std::int64_t c) {
  trace().push_back(static_cast<std::uint64_t>(c));
  return c;
}

inline std::uint64_t combine(std::uint64_t b, std::uint64_t a1,
                             std::uint64_t a2) {
  return a1 * 100 + b * 10 + a2;
}

// How many times a buffer was copied.
inline int &copies() {
  static int n = 0;
  return n;
}

struct buffer {
  std::vector<std::uint64_t> items;
  buffer() = default;
  buffer(const buffer &o) : items(o.items) { ++copies(); }
  buffer(buffer &&) noexcept = default;
  buffer &operator=(const buffer &o) {
    items = o.items;
    ++copies();
    return *this;
  }
  buffer &operator=(buffer &&) noexcept = default;
};

// Takes the buffer by value: an rvalue argument is moved in, an lvalue
// copied.
inline buffer push(buffer b, std::uint64_t x) {
  b.items.push_back(x);
  return b;
}

inline std::shared_ptr<std::int64_t>
poke(const std::shared_ptr<std::int64_t> &c, std::uint64_t n) {
  *c += static_cast<std::int64_t>(n);
  return c;
}

} // namespace ops_support
