#ifndef INCLUDED_UNDEDUCIBLE_TT_RETURN
#define INCLUDED_UNDEDUCIBLE_TT_RETURN

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <template <typename> class E, template <typename> class F, typename X>
struct Sum1;
template <typename X> struct ReqA;
template <typename X> struct ReqB;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <template <typename> class E, template <typename> class F, typename X>
struct Sum1 {
  // TYPES
  struct Inl1 {
    E<X> e;
  };

  struct Inr1 {
    F<X> f;
  };

  using variant_t = std::variant<Inl1, Inr1>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum1() {}

  explicit Sum1(Inl1 _v) : v_(std::move(_v)) {}

  explicit Sum1(Inr1 _v) : v_(std::move(_v)) {}

  template <template <typename> class _U0, template <typename> class _U1,
            typename _U2>
  Sum1(const Sum1<_U0, _U1, _U2> &_other) {
    if (std::holds_alternative<typename Sum1<_U0, _U1, _U2>::Inl1>(
            _other.v())) {
      const auto &[e] =
          std::get<typename Sum1<_U0, _U1, _U2>::Inl1>(_other.v());
      this->v_ = Inl1{E<X>(e)};
    } else {
      const auto &[f] =
          std::get<typename Sum1<_U0, _U1, _U2>::Inr1>(_other.v());
      this->v_ = Inr1{F<X>(f)};
    }
  }

  static Sum1<E, F, X> inl1(E<X> e) {
    return Sum1<E, F, X>(Inl1{std::move(e)});
  }

  static Sum1<E, F, X> inr1(F<X> f) {
    return Sum1<E, F, X>(Inr1{std::move(f)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Handler {
  template <template <typename> class T1, template <typename> class T2,
            typename T4, typename F0, typename F1>
  static std::invoke_result_t<F0 &, T1<T4> &> case_(F0 &&f, F1 &&g,
                                                    const Sum1<T1, T2, T4> &ab);
};

template <typename X> struct ReqA {
  // DATA
  X x;

  // ACCESSORS
  ReqA<X> clone() const { return {x}; }

  template <typename _U> operator ReqA<_U>() const {
    return {[&]() -> _U {
      if constexpr (std::is_same_v<X, std::any>) {
        return crane_any_cast<_U>(x);
      } else {
        if constexpr (std::is_constructible_v<_U, const X &>) {
          return _U(x);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }
    }()};
  }

  // CREATORS
  static ReqA<X> mka(X x) { return {std::move(x)}; }
};

template <typename X> struct ReqB {
  // DATA
  X x;

  // ACCESSORS
  ReqB<X> clone() const { return {x}; }

  template <typename _U> operator ReqB<_U>() const {
    return {[&]() -> _U {
      if constexpr (std::is_same_v<X, std::any>) {
        return crane_any_cast<_U>(x);
      } else {
        if constexpr (std::is_constructible_v<_U, const X &>) {
          return _U(x);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }
    }()};
  }

  // CREATORS
  static ReqB<X> mkb(X x) { return {std::move(x)}; }
};

struct UndeducibleTtReturn {
  static std::optional<Nat> use(const Sum1<ReqA, ReqB, Nat> &ab);
};

template <template <typename> class T1, template <typename> class T2,
          typename T4, typename F0, typename F1>
std::invoke_result_t<F0 &, T1<T4> &>
Handler::case_(F0 &&f, F1 &&g, const Sum1<T1, T2, T4> &ab) {
  if (std::holds_alternative<typename Sum1<T1, T2, T4>::Inl1>(ab.v())) {
    const auto &[e0] = std::get<typename Sum1<T1, T2, T4>::Inl1>(ab.v());
    return f(e0);
  } else {
    const auto &[f0] = std::get<typename Sum1<T1, T2, T4>::Inr1>(ab.v());
    return g(f0);
  }
}

#endif // INCLUDED_UNDEDUCIBLE_TT_RETURN
