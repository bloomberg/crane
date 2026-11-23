// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// C++ side of the loopify_final_move test: a copy-counting buffer.
#pragma once

#include <cstdint>
#include <vector>

namespace final_move_support {

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

} // namespace final_move_support
