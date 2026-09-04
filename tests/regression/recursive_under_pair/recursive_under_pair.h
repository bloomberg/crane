#ifndef INCLUDED_RECURSIVE_UNDER_PAIR
#define INCLUDED_RECURSIVE_UNDER_PAIR

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A constructor field holding the inductive under a pair
/// (N : (nat * c) -> c) is stored as shared_ptr<pair<uint64_t, c>>.  The
/// pattern match must dereference the pointer before projecting .second.
struct RecursiveUnderPair {
  struct c {
    // TYPES
    struct Stop {};

    struct N {
      std::shared_ptr<std::pair<uint64_t, c>> a0;
    };

    using variant_t = std::variant<Stop, N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    c() {}

    explicit c(Stop _v) : v_(_v) {}

    explicit c(N _v) : v_(std::move(_v)) {}

    static c stop() { return c(Stop{}); }

    static c n(std::pair<uint64_t, c> a0) {
      return c(N{std::make_shared<std::pair<uint64_t, c>>(std::move(a0))});
    }

    // MANIPULATORS
    ~c() {
      crane::small_vector<std::shared_ptr<c>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<N>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(std::make_shared<c>(std::move(_alt->a0->second)));
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

    c(const c &) = default;
    c &operator=(const c &) = default;
    c(c &&) noexcept = default;
    c &operator=(c &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<uint64_t, c> &>
  static T1 c_rect(T1 f, F1 &&f0, const c &c0) {
    if (std::holds_alternative<typename c::Stop>(c0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename c::N>(c0.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<uint64_t, c> &>
  static T1 c_rec(T1 f, F1 &&f0, const c &c0) {
    if (std::holds_alternative<typename c::Stop>(c0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename c::N>(c0.v());
      return f0(*a0);
    }
  }

  static c build(uint64_t n);
  static uint64_t depth(const c &x);
  static inline const uint64_t go = depth(build(UINT64_C(1000)));
};

#endif // INCLUDED_RECURSIVE_UNDER_PAIR
