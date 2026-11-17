// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::shared_array<T>: an immutable array shared by reference, the
// representation OCaml gives a Rocq sequence mapped to [array].
//
// A value is one word: the address of a counted block holding the length
// and the elements, or null for the empty array.  Copying is a count bump
// and indexing is O(1); building a new array from an old one -- an element
// put in front, the first ones dropped -- copies it, as [Array.append] and
// [Array.sub] do.  Meant for a sequence built once and then only read, such
// as a lexer's transition table.

#ifndef INCLUDED_CRANE_SHARED_ARRAY
#define INCLUDED_CRANE_SHARED_ARRAY

#include <cstddef>
#include <new>
#include <utility>

#include "shared_block.h"

namespace crane {

CRANE_RC_POLICY_BEGIN

template <class T> class shared_array {
  struct block : shared_block {
    std::size_t n;

    // The elements follow the header, at T's alignment.
    static constexpr std::size_t offset =
        (sizeof(shared_block) + sizeof(std::size_t) + alignof(T) - 1) / alignof(T) * alignof(T);
    T *data() noexcept { return reinterpret_cast<T *>(reinterpret_cast<char *>(this) + offset); }

    static void drop(const void *b, pool_detail::thread_heap &h) noexcept {
      auto *self = static_cast<block *>(const_cast<shared_block *>(static_cast<const shared_block *>(b)));
      T *d = self->data();
      for (std::size_t i = 0; i < self->n; ++i) {
        crane::release_into(d[i], h);
        d[i].~T();
      }
      self->~block();
      ::operator delete(self);
    }
  };

  block *p_ = nullptr;

  // A fresh array of [n] elements, the [i]th built by [put(slot, i)].
  template <class Put> static shared_array make(std::size_t n, Put &&put) {
    shared_array a;
    if (n == 0) return a;
    void *mem = ::operator new(block::offset + n * sizeof(T));
    auto *b = ::new (mem) block{{{}, &block::drop}, 0};
    T *d = b->data();
    for (std::size_t i = 0; i < n; ++i, ++b->n) put(d + i, i);
    a.p_ = b;
    return a;
  }

public:
  // A copy is a count bump.
  using crane_cheap_copy = void;

  shared_array() = default;
  shared_array(const shared_array &o) noexcept : p_(o.p_) {
    if (p_) p_->retain();
  }
  shared_array(shared_array &&o) noexcept : p_(std::exchange(o.p_, nullptr)) {}
  shared_array &operator=(shared_array o) noexcept {
    std::swap(p_, o.p_);
    return *this;
  }
  ~shared_array() {
    if (p_) p_->release();
  }

  // The array of the elements of [r], in order: [Array.of_list].
  template <class Range> static shared_array of_range(const Range &r) {
    std::size_t n = 0;
    for (auto it = r.begin(); it != r.end(); ++it) ++n;
    auto it = r.begin();
    return make(n, [&](T *slot, std::size_t) { ::new (slot) T(*it); ++it; });
  }

  std::size_t size() const noexcept { return p_ ? p_->n : 0; }
  bool empty() const noexcept { return p_ == nullptr; }
  const T &operator[](std::size_t i) const noexcept { return p_->data()[i]; }
  const T &front() const noexcept { return p_->data()[0]; }
  const T *begin() const noexcept { return p_ ? p_->data() : nullptr; }
  const T *end() const noexcept { return p_ ? p_->data() + p_->n : nullptr; }

  // [x] followed by this array's elements.
  shared_array push_front(const T &x) const {
    return make(size() + 1, [&](T *slot, std::size_t i) { ::new (slot) T(i == 0 ? x : (*this)[i - 1]); });
  }
  // This array without its first [k] elements.
  shared_array drop(std::size_t k) const {
    std::size_t n = size() > k ? size() - k : 0;
    return make(n, [&](T *slot, std::size_t i) { ::new (slot) T((*this)[i + k]); });
  }

  // [crane::release_into]: the block released into [h], this array empty.
  void release_into(pool_detail::thread_heap &h) noexcept {
    if (p_) p_->release_into(h);
    p_ = nullptr;
  }
};

CRANE_RC_POLICY_END

} // namespace crane

#endif // INCLUDED_CRANE_SHARED_ARRAY
