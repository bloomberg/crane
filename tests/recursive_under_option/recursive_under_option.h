#ifndef INCLUDED_RECURSIVE_UNDER_OPTION
#define INCLUDED_RECURSIVE_UNDER_OPTION

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct RecursiveUnderOption {
  struct c {
    // TYPES
    struct N {
      std::shared_ptr<std::optional<c>> a0;
    };

    using variant_t = std::variant<N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    c() {}

    explicit c(N _v) : v_(std::move(_v)) {}

    static c n(std::optional<c> a0) {
      return c(N{std::make_shared<std::optional<c>>(std::move(a0))});
    }

    // MANIPULATORS
    ~c() {
      crane::small_vector<std::shared_ptr<c>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<N>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (((*(_alt->a0))).has_value()) {
              _stack.push_back(
                  std::make_shared<c>(std::move((*((*(_alt->a0)))))));
            }
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::optional<c> &>
  static T1 c_rect(F0 &&f, const c &c0) {
    const auto &[a0] = std::get<typename c::N>(c0.v());
    return f(*a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::optional<c> &>
  static T1 c_rec(F0 &&f, const c &c0) {
    const auto &[a0] = std::get<typename c::N>(c0.v());
    return f(*a0);
  }

  static c build(uint64_t n);
  static uint64_t depth(const c &x);
  static inline const uint64_t go = depth(build(UINT64_C(1000)));
};

#endif // INCLUDED_RECURSIVE_UNDER_OPTION
