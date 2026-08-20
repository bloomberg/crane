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
// inline storage (no heap allocation at all) and only spills to a
// heap-allocated std::vector<T> once more than N elements are live
// simultaneously.
//
// The same reasoning applies to loopify's frame stack (make_loop_and_return):
// a loopified function pushes one frame per level of the recursion it
// replaced, so shallow recursions -- the common case -- never leave inline
// storage, where a std::vector always paid one heap allocation per call.
//
// This type is intentionally minimal: it supports exactly the operations
// the drain-worklist and frame-stack codegen use (push_back, emplace_back,
// back, pop_back, empty) and nothing else. It is not copyable (not needed by
// any generated use site); it is not intended as a general-purpose container.
//
// Correctness note: T is typically crane::rc<T'> (a refcounted pointer) or
// std::any wrapping one. All transitions between inline and heap storage
// move-construct into the new slot and then destroy (never copy) the old
// slot, so each logical element's ownership/refcount is transferred exactly
// once at every step -- no double-decrement, no leak.

#include <array>
#include <cstddef>
#include <memory>
#include <new>
#include <utility>
#include <vector>

namespace crane {

template <typename T, std::size_t N = 8> class small_vector {
public:
  small_vector() noexcept = default;

  small_vector(const small_vector &) = delete;
  small_vector &operator=(const small_vector &) = delete;
  small_vector(small_vector &&) = delete;
  small_vector &operator=(small_vector &&) = delete;

  ~small_vector() {
    if (heap_) {
      delete heap_;
    } else {
      for (std::size_t i = 0; i < inline_size_; ++i) {
        inline_ptr(i)->~T();
      }
    }
  }

  bool empty() const noexcept {
    return heap_ ? heap_->empty() : inline_size_ == 0;
  }

  void push_back(T &&v) { emplace_back(std::move(v)); }

  template <typename... Args> void emplace_back(Args &&...args) {
    if (heap_) {
      heap_->emplace_back(std::forward<Args>(args)...);
      return;
    }
    if (inline_size_ < N) {
      ::new (static_cast<void *>(inline_ptr(inline_size_)))
          T(std::forward<Args>(args)...);
      ++inline_size_;
      return;
    }
    // Spill: move every inline element into a fresh heap vector, destroying
    // the inline copies as we go, then append the new element.
    std::vector<T> *h = new std::vector<T>();
    h->reserve(N + 1);
    for (std::size_t i = 0; i < N; ++i) {
      h->push_back(std::move(*inline_ptr(i)));
      inline_ptr(i)->~T();
    }
    inline_size_ = 0;
    h->emplace_back(std::forward<Args>(args)...);
    heap_ = h;
  }

  T &back() { return heap_ ? heap_->back() : *inline_ptr(inline_size_ - 1); }

  void pop_back() {
    if (heap_) {
      heap_->pop_back();
      return;
    }
    --inline_size_;
    inline_ptr(inline_size_)->~T();
  }

private:
  T *inline_ptr(std::size_t i) noexcept {
    return std::launder(reinterpret_cast<T *>(&inline_storage_[i]));
  }

  alignas(T) std::array<unsigned char, sizeof(T)> inline_storage_[N];
  std::size_t inline_size_ = 0;
  std::vector<T> *heap_ = nullptr;
};

} // namespace crane
