#ifndef INCLUDED_SUM_DRAIN
#define INCLUDED_SUM_DRAIN

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A, typename B> struct Sum;

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename _U0, typename _U1> Sum(const Sum<_U0, _U1> &_other) {
    if (std::holds_alternative<typename Sum<_U0, _U1>::Inl>(_other.v())) {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inl>(_other.v());
      this->v_ = Inl{[&]() -> A {
        if constexpr (std::is_same_v<_U0, std::any>)
          return crane_any_cast<A>(a0);
        else
          return A(a0);
      }()};
    } else {
      const auto &[a0] = std::get<typename Sum<_U0, _U1>::Inr>(_other.v());
      this->v_ = Inr{[&]() -> B {
        if constexpr (std::is_same_v<_U1, std::any>)
          return crane_any_cast<B>(a0);
        else
          return B(a0);
      }()};
    }
  }

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct SumDrain {
  struct t {
    // TYPES
    struct N {
      std::shared_ptr<Sum<uint64_t, t>> a0;
    };

    using variant_t = std::variant<N>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(N _v) : v_(std::move(_v)) {}

    static t n(Sum<uint64_t, t> a0) {
      return t(N{std::make_shared<Sum<uint64_t, t>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<N>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (auto *_ha2 = std::get_if<typename Sum<uint64_t, t>::Inr>(
                    &(*_alt->a0).v_mut())) {
              _stack.push_back(std::make_shared<t>(std::move(_ha2->a0)));
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Sum<uint64_t, t> &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0] = std::get<typename t::N>(t0.v());
    return f(*a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, Sum<uint64_t, t> &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[a0] = std::get<typename t::N>(t0.v());
    return f(*a0);
  }

  static t build(uint64_t n, t acc);
  static uint64_t depth(const t &x);
  static uint64_t go(uint64_t n);
};

#endif // INCLUDED_SUM_DRAIN
