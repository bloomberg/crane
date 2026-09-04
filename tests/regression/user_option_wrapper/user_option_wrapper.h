#ifndef INCLUDED_USER_OPTION_WRAPPER
#define INCLUDED_USER_OPTION_WRAPPER

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct UserOptionWrapper {
  template <typename A> struct opt {
    // TYPES
    struct Non {};

    struct So {
      A a0;
    };

    using variant_t = std::variant<Non, So>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    opt() {}

    explicit opt(Non _v) : v_(_v) {}

    explicit opt(So _v) : v_(std::move(_v)) {}

    template <typename _U> opt(const opt<_U> &_other) {
      if (std::holds_alternative<typename opt<_U>::Non>(_other.v())) {
        this->v_ = Non{};
      } else {
        const auto &[a0] = std::get<typename opt<_U>::So>(_other.v());
        this->v_ = So{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>)
            return crane_any_cast<A>(a0);
          else
            return A(a0);
        }()};
      }
    }

    static opt<A> non() { return opt<A>(Non{}); }

    static opt<A> so(A a0) { return opt<A>(So{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    T1 opt_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename opt<A>::Non>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename opt<A>::So>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    T1 opt_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename opt<A>::Non>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename opt<A>::So>(this->v());
        return f0(a0);
      }
    }
  };

  struct t {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<opt<t>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(uint64_t a0, opt<t> a1) {
      return t(Node{a0, std::make_shared<opt<t>>(std::move(a1))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (auto *_ha2 =
                    std::get_if<typename UserOptionWrapper::opt<t>::So>(
                        &((*(_alt->a1))).v_mut())) {
              _stack.push_back(std::make_shared<t>(std::move(_ha2->a0)));
            }
            _alt->a1.reset();
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

    t wrap(uint64_t k) const {
      return t::node(k, opt<t>::so(std::move(*this)));
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, opt<t> &>
    T1 t_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename t::Node>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, opt<t> &>
    T1 t_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename t::Node>(this->v());
      return f(a0, *a1);
    }
  };

  static inline const t empty = t::node(UINT64_C(0), opt<t>::non());
};

#endif // INCLUDED_USER_OPTION_WRAPPER
