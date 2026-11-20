// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include "structural_spans.h"

#include <iostream>
#include <span>
#include <type_traits>
#include <vector>

namespace {

int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}

template <typename T> std::vector<T> to_vector(const List<T> &l) {
  std::vector<T> out;
  const List<T> *cur = &l;
  while (const auto *cell = std::get_if<typename List<T>::Cons>(&cur->v())) {
    out.push_back(cell->a);
    if (!cell->l) {
      break;
    }
    cur = cell->l.get();
  }
  return out;
}

using Read = std::span<const uint64_t>;
using Write = std::span<uint64_t>;
using Buffer = std::vector<uint64_t>;

// A read takes the read span, an element write the writable span, a helper
// that may reallocate the buffer itself by reference; a subspan escaping as
// a Buf is a copy.
static_assert(std::is_same_v<decltype(&StructuralSpans::total),
                             uint64_t (*)(Read)>);
static_assert(std::is_same_v<decltype(&StructuralSpans::bump),
                             void (*)(Write, uint64_t)>);
static_assert(std::is_same_v<decltype(&StructuralSpans::grow),
                             void (*)(Buffer &, uint64_t)>);
static_assert(std::is_same_v<decltype(&StructuralSpans::window_total),
                             uint64_t (*)(Read)>);
static_assert(std::is_same_v<decltype(&StructuralSpans::window),
                             Buffer (*)(Read)>);
static_assert(std::is_same_v<decltype(&StructuralSpans::self_append),
                             void (*)(Buffer &)>);

} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

int main() {
  {
    auto [rest, window] = StructuralSpans::scenario(5);
    auto [first, window_total] = rest;
    auto [elems, total] = first;
    ASSERT((to_vector(elems) ==
            std::vector<uint64_t>{7, 2, 1, 1, 1, 7, 2, 1, 1, 1}));
    ASSERT(total == 24);
    ASSERT(window_total == 3);
    ASSERT((to_vector(window) == std::vector<uint64_t>{2, 1}));
  }
  ASSERT(StructuralSpans::fresh_window_total(4) == 6);
  {
    // The window is a copy: it outlives the buffer it was taken from.
    Buffer w;
    {
      Buffer b{1, 2, 3, 4};
      w = StructuralSpans::window(Read{b});
    }
    ASSERT((w == Buffer{2, 3}));
  }
  {
    // Appending a buffer to itself reads a copy, not the storage the
    // append reallocates.
    Buffer b{1, 2, 3};
    StructuralSpans::self_append(b);
    ASSERT((b == Buffer{1, 2, 3, 1, 2, 3}));
  }
  if (testStatus == 0) {
    std::cout << "All structural_spans tests passed!" << std::endl;
  }
  return testStatus;
}
