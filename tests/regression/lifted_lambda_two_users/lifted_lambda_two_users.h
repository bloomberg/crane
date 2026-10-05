#ifndef INCLUDED_LIFTED_LAMBDA_TWO_USERS
#define INCLUDED_LIFTED_LAMBDA_TWO_USERS

#include "fn.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <utility>
#include <variant>

struct LiftedLambdaTwoUsers {
  struct t {
    // TYPES
    struct L {};

    struct N {
      std::shared_ptr<t> a0;
    };

    using variant_t = std::variant<L, N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(L _v) : v_(_v) {}

    explicit t(N _v) : v_(std::move(_v)) {}

    static t l() { return t(L{}); }

    static t n(t a0) { return t(N{std::make_shared<t>(std::move(a0))}); }

    // MANIPULATORS
    ~t() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<t> {
        if (auto *_alt = std::get_if<N>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<t> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) = default;
    t &operator=(t &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 t_rect(T1 f, F1 &&f0, const t &t0) {
    if (std::holds_alternative<typename t::L>(t0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename t::N>(t0.v());
      return f0(*a0, t_rect<T1>(std::move(f), f0, *a0));
    }
  }

  template <typename T1, typename F1>
  static T1 t_rec(T1 f, F1 &&f0, const t &t0) {
    return t_rect<T1>(std::move(f), f0, t0);
  }

  static uint64_t depth(const t &x);
  static inline const uint64_t one = []() {
    return []() {
      t x = t::n(t::l());
      crane::fn<uint64_t(uint64_t)> f = [=](uint64_t) { return depth(x); };
      return (f(UINT64_C(0)) + f(UINT64_C(1)));
    }();
  }();
  static inline const uint64_t two = []() {
    return []() {
      t y = t::n(t::n(t::l()));
      crane::fn<uint64_t(uint64_t)> g = [=](uint64_t) { return depth(y); };
      return (g(UINT64_C(0)) + g(UINT64_C(1)));
    }();
  }();
  static inline const uint64_t go = (one + two);
};

#endif // INCLUDED_LIFTED_LAMBDA_TWO_USERS
