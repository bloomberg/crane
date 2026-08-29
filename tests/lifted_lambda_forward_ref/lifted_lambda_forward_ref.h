#ifndef INCLUDED_LIFTED_LAMBDA_FORWARD_REF
#define INCLUDED_LIFTED_LAMBDA_FORWARD_REF

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct LiftedLambdaForwardRef {
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
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<N>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, t &, T1 &>
  static T1 t_rect(T1 f, F1 &&f0, const t &t0) {
    if (std::holds_alternative<typename t::L>(t0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename t::N>(t0.v());
      return f0(*a0, t_rect<T1>(f, f0, *a0));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, t &, T1 &>
  static T1 t_rec(T1 f, F1 &&f0, const t &t0) {
    if (std::holds_alternative<typename t::L>(t0.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename t::N>(t0.v());
      return f0(*a0, t_rec<T1>(f, f0, *a0));
    }
  }

  static uint64_t later(const t &x);

  template <typename T1> static uint64_t _anon_f(const T1, const t x) {
    return later(x);
  }

  static inline const uint64_t go = []() {
    t x = t::n(t::l());
    return (_anon_f(UINT64_C(0), x) + _anon_f(UINT64_C(1), x));
  }();
};

#endif // INCLUDED_LIFTED_LAMBDA_FORWARD_REF
