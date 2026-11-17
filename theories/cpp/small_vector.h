#pragma once


// crane::small_vector<T, N> -- a minimal small-buffer-optimized stack used
// by Crane's generated iterative-destructor "drain" worklists (see
// gen_decls.ml's mk_ctor_drain) and similar shallow, LIFO-only worklists.
//
// Rationale: destructor drain worklist depth tracks tree *height*, not tree
// *size*, so in the overwhelming majority of real inputs the worklist never
// holds more than a handful of pending nodes at once. Previously this was a
// plain std::vector<T> with reserve(8), which still performs exactly one
// heap allocation per destructor invocation even when the worklist never
// exceeds a couple of elements. small_vector keeps the first N elements in
// inline storage (no heap allocation at all) and only moves to the heap
// once more than N elements are live simultaneously.
//
// The same reasoning applies to loopify's frame stack (make_loop_and_return):
// a loopified function pushes one frame per level of the recursion it
// replaced, so shallow recursions -- the common case -- never leave inline
// storage, where a std::vector always paid one heap allocation per call.
// N is 32: a balanced tree of a few billion nodes, or a random search tree
// of tens of thousands, stays inline.
//
// The stack is three pointers into one buffer, the inline one or a heap one,
// so [back], [pop_back] and [emplace_back] are pointer bumps with no test of
// which buffer is in use; only a full buffer takes the out-of-line path,
// which doubles it.
//
// This type is intentionally minimal: it supports exactly the operations
// the drain-worklist and frame-stack codegen use (push_back, emplace_back,
// back, pop_back, empty) and nothing else. It is not copyable (not needed by
// any generated use site); it is not intended as a general-purpose container.
//
// Correctness note: T is typically crane::rc<T'> (a refcounted pointer) or
// std::any wrapping one. Growing move-constructs every element into the new
// buffer and then destroys (never copies) the old one, so each logical
// element's ownership/refcount is transferred exactly once at every step --
// no double-decrement, no leak.

#include <cstddef>
#include <memory>
#include <new>
#include <utility>

namespace crane {

template <typename T, std::size_t N = 32> class small_vector {
public:
  small_vector() noexcept : begin_(inline_ptr()), end_(begin_), cap_(begin_ + N) {}

  small_vector(const small_vector &) = delete;
  small_vector &operator=(const small_vector &) = delete;
  small_vector(small_vector &&) = delete;
  small_vector &operator=(small_vector &&) = delete;

  ~small_vector() {
    std::destroy(begin_, end_);
    if (begin_ != inline_ptr()) release(begin_);
  }

  bool empty() const noexcept { return end_ == begin_; }

  void push_back(T &&v) { emplace_back(std::move(v)); }

  template <typename... Args> void emplace_back(Args &&...args) {
    if (end_ == cap_) [[unlikely]] grow();
    ::new (static_cast<void *>(end_)) T(std::forward<Args>(args)...);
    ++end_;
  }

  T &back() noexcept { return end_[-1]; }

  void pop_back() noexcept {
    --end_;
    end_->~T();
  }

private:
  T *inline_ptr() noexcept { return std::launder(reinterpret_cast<T *>(inline_storage_)); }

  static void release(T *p) noexcept { ::operator delete(p, std::align_val_t{alignof(T)}); }

  [[gnu::noinline]] void grow() {
    std::size_t n = static_cast<std::size_t>(end_ - begin_);
    T *fresh = static_cast<T *>(::operator new(2 * n * sizeof(T), std::align_val_t{alignof(T)}));
    std::uninitialized_move(begin_, end_, fresh);
    std::destroy(begin_, end_);
    if (begin_ != inline_ptr()) release(begin_);
    begin_ = fresh;
    end_ = fresh + n;
    cap_ = fresh + 2 * n;
  }

  T *begin_;
  T *end_;
  T *cap_;
  alignas(T) unsigned char inline_storage_[N * sizeof(T)];
};

} // namespace crane
