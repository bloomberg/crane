#ifndef INCLUDED_LOOP_TRANSFORM_REASSIGNS_CLOSURE_TYPED_VAR
#define INCLUDED_LOOP_TRANSFORM_REASSIGNS_CLOSURE_TYPED_VAR

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct Lst;

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

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
};

template <typename A> struct Lst {
  // TYPES
  struct Nil {};

  struct Cons {
    A x;
    std::shared_ptr<Lst<A>> xs;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Lst() {}

  explicit Lst(Nil _v) : v_(_v) {}

  explicit Lst(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> Lst(const Lst<_U> &_other) {
    if (std::holds_alternative<typename Lst<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[x, xs] = std::get<typename Lst<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(x);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (xs ? std::make_shared<Lst<A>>(crane_convert<Lst<A>>(*xs))
                   : nullptr)};
    }
  }

  static Lst<A> nil() { return Lst<A>(Nil{}); }

  static Lst<A> cons(A x, Lst<A> xs) {
    return Lst<A>(Cons{std::move(x), std::make_shared<Lst<A>>(std::move(xs))});
  }

  // MANIPULATORS
  ~Lst() {
    crane::small_vector<std::shared_ptr<Lst<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->xs) {
          _stack.push_back(std::move(_alt->xs));
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

  Lst(const Lst &) = default;
  Lst &operator=(const Lst &) = default;
  Lst(Lst &&) noexcept = default;
  Lst &operator=(Lst &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  /// The callable takes a membership proof, so the recursive call cannot pass
  /// it through unchanged.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  Lst<T1> map_In(F0 &&f) const {
    std::shared_ptr<Lst<T1>> _head{};
    std::shared_ptr<Lst<T1>> *_write = &_head;
    const Lst<A> *_loop_self = this;
    std::function<T1(A)> _loop_f = f;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Lst<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<Lst<T1>>(Lst<T1>::nil());
        break;
      } else {
        const auto &[x0, xs0] = std::get<typename Lst<A>::Cons>(_sv.v());
        const Lst<A> &xs0_value = *xs0;
        auto _cell = std::make_shared<Lst<T1>>(
            typename Lst<T1>::Cons(_loop_f(x0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Lst<T1>::Cons>((*_write)->v_mut()).xs;
        _loop_self = &xs0_value;
        _loop_f = [=](const A &y) mutable { return _loop_f(y); };
        continue;
      }
    }
    return std::move(*_head);
  }

  Lst<Nat> go(Nat n) const {
    return this->template map_In<Nat>(
        [=](const Nat &x) mutable { return x.add(n); });
  }
};

/// Takes a unit so that Crane leaves it a free function and something
/// concrete instantiates map_In.
Lst<Nat> run(std::monostate _x);

#endif // INCLUDED_LOOP_TRANSFORM_REASSIGNS_CLOSURE_TYPED_VAR
