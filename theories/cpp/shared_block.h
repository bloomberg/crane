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
#include "pool.h"
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

// A count at [immortal] is never changed, so its block is never freed and
// no thread writes it: a constant ([crane::constant]) is read from every
// thread, non-atomic counts or not.
inline constexpr std::size_t immortal = ~std::size_t{0};

#ifdef CRANE_NON_ATOMIC_RC
struct count {
  std::size_t n{1};
  void inc() noexcept {
    if (n != immortal) ++n;
  }
  bool dec() noexcept { return n != immortal && --n == 0; }
  bool sole() const noexcept { return n == 1; }
  void make_immortal() noexcept { n = immortal; }
};
#else
struct count {
  std::atomic<std::size_t> n{1};
  void inc() noexcept {
    if (n.load(std::memory_order_relaxed) != immortal) n.fetch_add(1, std::memory_order_relaxed);
  }
  bool dec() noexcept {
    return n.load(std::memory_order_relaxed) != immortal
           && n.fetch_sub(1, std::memory_order_acq_rel) == 1;
  }
  bool sole() const noexcept { return n.load(std::memory_order_acquire) == 1; }
  void make_immortal() noexcept { n.store(immortal, std::memory_order_relaxed); }
};
#endif

// Frees a block whose count reached zero without recursing into what it
// held.  A block's destructor releases what it captured, which may free
// another block, and so on down a chain as long as the program's longest
// continuation or tree: freed recursively, that is one C++ frame per link.
// Instead a free that happens while another is running is queued on the
// thread's heap (pool.h), and the outermost one drains the queue.
[[gnu::noinline]] inline void
free_block(const void *block, pool_detail::destroy_fn destroy) noexcept {
  pool_detail::thread_heap &h = pool_detail::this_thread_heap();
  if (h.draining) {
    h.push({block, destroy});
    return;
  }
  h.draining = true;
  destroy(block, h);
  while (h.size != 0) {
    pool_detail::pending_free f = h.items[--h.size];
    f.destroy(f.block, h);
  }
  h.draining = false;
}

} // namespace block_detail

// What a shared block starts with.  [destroy] is a function pointer rather
// than a virtual destructor so the header is two words and what the block
// holds follows it directly; it is handed the heap the block goes back to.
struct shared_block {
  mutable block_detail::count rc;
  const pool_detail::destroy_fn destroy;

  void retain() const noexcept { rc.inc(); }
  // Drops one reference; the last one frees the block, out of line, so the
  // decrement and test are all that is inlined where a reference dies.
  void release() const noexcept {
    if (rc.dec())
      block_detail::free_block(this, destroy);
  }
};

CRANE_RC_POLICY_END

} // namespace crane
