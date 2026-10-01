// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// The header every shared runtime block starts with: a reference count and
// the function that destroys the block.  A closure ([crane::fn]), an erased
// value's box ([crane::obj]) and a coinductive's cell ([crane::lazy]) are all
// one such block followed by what they hold.
//
// The count is non-atomic when the generated header defines
// CRANE_NON_ATOMIC_RC (the [Crane NonAtomicRc] policy, withheld from units
// that spawn threads), and atomic otherwise.  Every type whose layout holds a
// count is declared inside CRANE_RC_POLICY_BEGIN / CRANE_RC_POLICY_END, an
// inline namespace named after the policy, so the two disciplines are
// different types: a program that passes a block from a unit compiled under
// one policy to a unit compiled under the other fails to link instead of
// sharing a count between them.
//
// Within one translation unit the policy is whichever the first runtime
// header saw.  A unit that spawns threads checks [crane::rc_is_atomic] after
// its includes, so a non-atomic header included ahead of it is a compile
// error rather than a race.
#pragma once
#include <cstddef>
#include <new>
#ifndef CRANE_NON_ATOMIC_RC
#include <atomic>
#endif

#ifdef CRANE_NON_ATOMIC_RC
#define CRANE_RC_POLICY_BEGIN inline namespace rc_local {
#else
#define CRANE_RC_POLICY_BEGIN inline namespace rc_shared {
#endif
#define CRANE_RC_POLICY_END }

namespace crane {

#ifdef CRANE_NON_ATOMIC_RC
inline constexpr bool rc_is_atomic = false;
#else
inline constexpr bool rc_is_atomic = true;
#endif

CRANE_RC_POLICY_BEGIN

namespace block_detail {

#ifdef CRANE_NON_ATOMIC_RC
struct count {
  std::size_t n{1};
  void inc() noexcept { ++n; }
  bool dec() noexcept { return --n == 0; }
  bool sole() const noexcept { return n == 1; }
};
#else
struct count {
  std::atomic<std::size_t> n{1};
  void inc() noexcept { n.fetch_add(1, std::memory_order_relaxed); }
  bool dec() noexcept { return n.fetch_sub(1, std::memory_order_acq_rel) == 1; }
  bool sole() const noexcept { return n.load(std::memory_order_acquire) == 1; }
};
#endif

// Frees a block whose count reached zero without recursing into what it
// held.  A block's destructor releases what it captured, which may free
// another block, and so on down a chain as long as the program's longest
// continuation or tree: freed recursively, that is one C++ frame per link.
// Instead a free that happens while another is running is queued, and the
// outermost one drains the queue.
struct pending_free {
  const void *block;
  void (*destroy)(const void *) noexcept;
};
//
// The queue has no destructor: a value in a static is freed after the
// thread's own thread_local objects are gone, so the queue must still work
// then.  Its buffer lives as long as the thread.
struct free_queue {
  bool draining = false;
  pending_free *items = nullptr;
  std::size_t size = 0, cap = 0;
  void push(pending_free f) {
    if (size == cap) {
      std::size_t ncap = cap ? cap * 2 : 64;
      auto *n = static_cast<pending_free *>(
          ::operator new(ncap * sizeof(pending_free)));
      for (std::size_t i = 0; i < size; ++i)
        n[i] = items[i];
      ::operator delete(items);
      items = n;
      cap = ncap;
    }
    items[size++] = f;
  }
};
inline free_queue &frees() noexcept {
  static constinit thread_local free_queue q;
  return q;
}
inline void free_block(const void *block,
                       void (*destroy)(const void *) noexcept) noexcept {
  free_queue &q = frees();
  if (q.draining) {
    q.push({block, destroy});
    return;
  }
  q.draining = true;
  destroy(block);
  while (q.size != 0) {
    pending_free f = q.items[--q.size];
    f.destroy(f.block);
  }
  q.draining = false;
}

} // namespace block_detail

// What a shared block starts with.  [destroy] is a function pointer rather
// than a virtual destructor so the header is two words and what the block
// holds follows it directly.
struct shared_block {
  mutable block_detail::count rc;
  void (*const destroy)(const void *) noexcept;

  void retain() const noexcept { rc.inc(); }
  // Drops one reference; the last one frees the block.
  void release() const noexcept {
    if (rc.dec())
      block_detail::free_block(this, destroy);
  }
};

CRANE_RC_POLICY_END

} // namespace crane
