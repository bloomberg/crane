// Copyright 2025 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// The thread's heap: every small runtime block -- each closure, each
// coinductive's node, each generated inductive's control block, each boxed
// field -- is allocated from, and freed to, the heap of the thread doing it.
//
// The heap is one thread_local object, and it holds everything the
// allocator and the deallocator touch: free lists by size, and the queue of
// frees waiting to run (shared_block.h).  One object, because reaching a
// thread_local is not free: on Darwin every access is a call through the
// variable's descriptor, and a block that kept its free list and the queue
// in separate thread_locals paid for three such calls in its lifetime, a
// tenth of an interpreter's running time.  A free that runs from the queue
// is handed the heap, so it returns its memory without looking it up again.
//
// A block's size class is a compile-time constant: [pooled<Derived>] gives
// [Derived] an [operator new]/[operator delete] that pop and push the list
// for [sizeof(Derived)] rounded up to a 16-byte class.  Blocks of one class
// are interchangeable whatever type they held, so the memory a dead closure
// leaves is reused by the next node of the same size.  A freed block never
// goes back to the system allocator; the same shapes recur constantly in a
// running interpreter, so the lists are worth keeping full.
//
// Safe across threads without any atomics of its own: a block freed on a
// different thread than the one that allocated it lands on that thread's
// own list, which is merely a missed reuse, never a race -- the list a
// thread pops from is the same one only that thread ever pushes to.
//
// The lists are not capped.  A thread that only frees what another allocates
// grows its list without bound; a cap was tried, and the counter it needs on
// every allocation and free, with the bursts past it going back to malloc,
// cost Vellvm 7-13% across the board.
#pragma once
#include <cstddef>
#include <new>

namespace crane {

class arena;

namespace pool_detail {

struct thread_heap;

// A free that happens while another is running; see [free_block] in
// shared_block.h.
using destroy_fn = void (*)(const void *, thread_heap &) noexcept;
struct pending_free {
  const void *block;
  destroy_fn destroy;
};

inline constexpr std::size_t grain = 16;
inline constexpr std::size_t classes = 32; // pooled blocks are at most 512 bytes

template <std::size_t Size>
inline constexpr std::size_t class_of = (Size + grain - 1) / grain - 1;

#ifdef CRANE_COUNT_TAKES
// Measurement only: every block handed out, fresh or recycled, so a test can
// count allocations that the free lists hide from [operator new].
inline std::size_t takes = 0;
#endif

// The heap has no destructor: a value in a static is freed after the
// thread's own thread_local objects are gone, so the heap must still work
// then.  Its lists and its queue's buffer live as long as the thread.
struct thread_heap {
  void *lists[classes] = {};

  bool draining = false;
  pending_free *items = nullptr;
  std::size_t size = 0, cap = 0;

  // The region an open [arena_scope] allocates from (arena.h), if any.
  arena *open_arena = nullptr;

  template <std::size_t Size> void *take() {
#ifdef CRANE_COUNT_TAKES
    ++takes;
#endif
    if constexpr (class_of<Size> >= classes) {
      return ::operator new(Size);
    } else {
      void *&head = lists[class_of<Size>];
      if (head) {
        void *p = head;
        head = *static_cast<void **>(p);
        return p;
      }
      // The whole class, so the block can serve any size in it later.
      return ::operator new((class_of<Size> + 1) * grain);
    }
  }
  template <std::size_t Size> void give(void *p) noexcept {
    if constexpr (class_of<Size> >= classes) {
      ::operator delete(p);
    } else {
      void *&head = lists[class_of<Size>];
      *static_cast<void **>(p) = head;
      head = p;
    }
  }

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

// The heap blocks come from and go back to: the thread's own, or under
// CRANE_SINGLE_THREADED ([Crane SingleThreaded], a program that uses Crane
// values from one thread at a time) one global -- on Darwin a thread-local
// access is a call, made by every allocation and free.  What reaches the heap
// is declared inside CRANE_HEAP_POLICY_BEGIN / CRANE_HEAP_POLICY_END, an
// inline namespace named after the policy, so units compiled under the two
// do not share a definition.
#ifdef CRANE_SINGLE_THREADED
#define CRANE_HEAP_POLICY_BEGIN inline namespace heap_single {
#else
#define CRANE_HEAP_POLICY_BEGIN inline namespace heap_per_thread {
#endif
#define CRANE_HEAP_POLICY_END }

CRANE_HEAP_POLICY_BEGIN

inline thread_heap &this_thread_heap() noexcept {
#ifdef CRANE_SINGLE_THREADED
  static constinit thread_heap h;
#else
  static constinit thread_local thread_heap h;
#endif
  return h;
}

template <typename Derived> struct pooled {
  static void *operator new(std::size_t) {
    // always sizeof(Derived): Derived has no virtual base, no tail.
    return this_thread_heap().take<sizeof(Derived)>();
  }
  static void operator delete(void *p, std::size_t) noexcept {
    this_thread_heap().give<sizeof(Derived)>(p);
  }

  // [delete p], for a free already holding the heap.
  static void dispose(const Derived *p, thread_heap &h) noexcept {
    if constexpr (alignof(Derived) > __STDCPP_DEFAULT_NEW_ALIGNMENT__) {
      delete p;
    } else {
      p->~Derived();
      h.give<sizeof(Derived)>(const_cast<Derived *>(p));
    }
  }

  // A type aligned more strictly than [operator new] guarantees is allocated
  // at its alignment and never pooled: a block from a list is only aligned
  // as far as the default [operator new] aligned it.
  static void *operator new(std::size_t n, std::align_val_t a) {
    return ::operator new(n, a);
  }
  static void operator delete(void *p, std::size_t, std::align_val_t a) noexcept {
    ::operator delete(p, a);
  }
};

CRANE_HEAP_POLICY_END

} // namespace pool_detail
} // namespace crane
