#ifndef INCLUDED_LOOPIFY_WRAPPER_RECEIVER
#define INCLUDED_LOOPIFY_WRAPPER_RECEIVER

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct LoopifyWrapperReceiver {
  template <typename A> struct box {
    // DATA
    A a0;

    // ACCESSORS
    box<A> clone() const { return {a0}; }

    // CREATORS
    static box<A> b(A a0) { return {std::move(a0)}; }

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

  struct t {
    // TYPES
    struct L {};

    struct N {
      std::shared_ptr<box<t>> a0;
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

    static t n(box<t> a0) {
      return t(N{std::make_shared<box<t>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<N>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(std::make_shared<t>(std::move(_alt->a0->a0)));
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    t build(uint64_t n) const {
      t _self_store;
      const t *_loop_self = this;
      uint64_t _loop_n = std::move(n);
      while (true) {
        if (_loop_n <= 0) {
          return std::move(*_loop_self);
        } else {
          uint64_t m = _loop_n - 1;
          _self_store = t::n(box<t>::b(std::move(*_loop_self)));
          _loop_self = &_self_store;
          _loop_n = m;
        }
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, box<t> &>
    T1 t_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename t::L>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename t::N>(this->v());
        return f0(*a0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, box<t> &>
    T1 t_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename t::L>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename t::N>(this->v());
        return f0(*a0);
      }
    }
  };

  static t mk(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_WRAPPER_RECEIVER
