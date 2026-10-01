// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// A per-type free list: [pooled<Derived>] gives [Derived] its own
// [operator new]/[operator delete], backed by a singly-linked list of
// exactly-[Derived]-sized blocks.  Every closure type, every coinductive's
// node type, and every generated inductive's control block is a distinct
// C++ instantiation, so this needs no runtime size-class lookup and no
// locking -- a thread_local pointer, popped or pushed, is the whole
// allocator.  A freed block never goes back to the system allocator; the
// same shapes recur constantly in a running interpreter (the same handful
// of continuation, node and cell types, over and over), so the list is
// worth keeping full.
//
// Safe across threads without any atomics of its own: a block freed on a
// different thread than the one that allocated it lands on that thread's
// own list, which is merely a missed reuse, never a race -- the list a
// thread pops from is the same one only that thread ever pushes to.
#pragma once
#include <cstddef>
#include <new>

namespace crane {
namespace pool_detail {

template <typename Derived> struct pooled {
  static void *operator new(std::size_t n) {
    void *&head = free_head();
    if (head) {
      void *p = head;
      head = *static_cast<void **>(p);
      return p;
    }
    (void)n; // always sizeof(Derived): Derived has no virtual base, no tail.
    return ::operator new(sizeof(Derived));
  }
  static void operator delete(void *p, std::size_t) noexcept {
    void *&head = free_head();
    *static_cast<void **>(p) = head;
    head = p;
  }

private:
  static void *&free_head() noexcept {
    static thread_local void *head = nullptr;
    return head;
  }
};

} // namespace pool_detail
} // namespace crane
