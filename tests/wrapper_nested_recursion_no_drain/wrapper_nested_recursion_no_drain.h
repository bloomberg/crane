#ifndef INCLUDED_WRAPPER_NESTED_RECURSION_NO_DRAIN
#define INCLUDED_WRAPPER_NESTED_RECURSION_NO_DRAIN

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct WrapperNestedRecursionNoDrain {
  template <typename A> struct box {
    // DATA
    A a0;

    // ACCESSORS
    box<A> clone() const { return {a0}; }

    // CREATORS
    static box<A> box0(A a0) { return {std::move(a0)}; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    T1 box_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    T1 box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  struct rose {
    // TYPES
    struct RLeaf {
      uint64_t a0;
    };

    struct RNode {
      std::shared_ptr<box<rose>> a0;
    };

    using variant_t = std::variant<RLeaf, RNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RLeaf _v) : v_(std::move(_v)) {}

    explicit rose(RNode _v) : v_(std::move(_v)) {}

    static rose rleaf(uint64_t a0) { return rose(RLeaf{a0}); }

    static rose rnode(box<rose> a0) {
      return rose(RNode{std::make_shared<box<rose>>(std::move(a0))});
    }

    // MANIPULATORS
    ~rose() {
      crane::small_vector<std::shared_ptr<rose>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<RNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(std::make_shared<rose>(std::move(_alt->a0->a0)));
            _alt->a0.reset();
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    rose(const rose &) = default;
    rose &operator=(const rose &) = default;
    rose(rose &&) noexcept = default;
    rose &operator=(rose &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, box<rose> &>
    T1 rose_rec(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename rose::RLeaf>(this->v())) {
        const auto &[a0] = std::get<typename rose::RLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename rose::RNode>(this->v());
        return f0(*a0);
      }
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, box<rose> &>
    T1 rose_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename rose::RLeaf>(this->v())) {
        const auto &[a0] = std::get<typename rose::RLeaf>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename rose::RNode>(this->v());
        return f0(*a0);
      }
    }
  };

  static rose deep(uint64_t n);
  static uint64_t test_deep(uint64_t n);
};

#endif // INCLUDED_WRAPPER_NESTED_RECURSION_NO_DRAIN
