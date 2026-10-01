// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// A per-type free list: [pooled<Derived>] gives [Derived] its own
// [operator new]/[operator delete], backed by a singly-linked list of
// exactly-[Derived]-sized blocks.  Every closure type, every coinductive's
// node type, and every generated inductive's control block is a distinct
// C++ instantiation, so this needs no runtime size-class lookup and no
// locking -- a thread_local pointer, popped or pushed, is the whole
// allocator.  A freed block goes back to the system allocator only past the
// list's cap; the same shapes recur constantly in a running interpreter (the
// same handful of continuation, node and cell types, over and over), so the
// list is worth keeping full.
//
// Safe across threads without any atomics of its own: a block freed on a
// different thread than the one that allocated it lands on that thread's
// own list, which is merely a missed reuse, never a race -- the list a
// thread pops from is the same one only that thread ever pushes to.  Each
// list is capped, so a thread that only frees does not grow without bound.
#pragma once
#include <cstddef>
#include <new>

namespace crane {
namespace pool_detail {

template <typename Derived> struct pooled {
  static void *operator new(std::size_t n) {
    list &l = free_list();
    if (l.head) {
      void *p = l.head;
      l.head = *static_cast<void **>(p);
      --l.length;
      return p;
    }
    (void)n; // always sizeof(Derived): Derived has no virtual base, no tail.
    return ::operator new(sizeof(Derived));
  }
  static void operator delete(void *p, std::size_t) noexcept {
    list &l = free_list();
    if (l.length == max_length) {
      ::operator delete(p);
      return;
    }
    *static_cast<void **>(p) = l.head;
    l.head = p;
    ++l.length;
  }

  // A type aligned more strictly than [operator new] guarantees is allocated
  // at its alignment and never pooled: a block from the list is only aligned
  // as far as the default [operator new] aligned it.
  static void *operator new(std::size_t n, std::align_val_t a) {
    return ::operator new(n, a);
  }
  static void operator delete(void *p, std::size_t, std::align_val_t a) noexcept {
    ::operator delete(p, a);
  }

private:
  // A thread that only frees what another thread allocated -- a consumer --
  // pushes onto its own list and never pops, so the list is capped: past
  // [max_length] a block goes back to the system allocator.
  static constexpr std::size_t max_length = 1 << 16;
  struct list {
    void *head = nullptr;
    std::size_t length = 0;
  };
  static list &free_list() noexcept {
    static thread_local list l;
    return l;
  }
};

} // namespace pool_detail
} // namespace crane
