#ifndef INCLUDED_BOXED_PAIR_FIELD_CONV_CTOR
#define INCLUDED_BOXED_PAIR_FIELD_CONV_CTOR

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
struct Dt;
template <typename T> struct Exp0;

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

struct Dt {
  // TYPES
  struct DI {
    Nat a0;
  };

  struct DP {};

  using variant_t = std::variant<DI, DP>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dt() {}

  explicit Dt(DI _v) : v_(std::move(_v)) {}

  explicit Dt(DP _v) : v_(_v) {}

  static Dt di(Nat a0) { return Dt(DI{std::move(a0)}); }

  static Dt dp() { return Dt(DP{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename T> struct Exp0 {
  // TYPES
  struct EV {
    T a0;
  };

  struct ESELF {
    std::shared_ptr<Exp0<T>> a0;
  };

  struct ENEG {
    std::shared_ptr<std::pair<T, Exp0<T>>> a0;
  };

  using variant_t = std::variant<EV, ESELF, ENEG>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Exp0() {}

  explicit Exp0(EV _v) : v_(std::move(_v)) {}

  explicit Exp0(ESELF _v) : v_(std::move(_v)) {}

  explicit Exp0(ENEG _v) : v_(std::move(_v)) {}

  template <typename _U> Exp0(const Exp0<_U> &_other) {
    if (std::holds_alternative<typename Exp0<_U>::EV>(_other.v())) {
      const auto &[a0] = std::get<typename Exp0<_U>::EV>(_other.v());
      this->v_ = EV{[&]() -> T {
        if constexpr (crane_convertible<T, const _U &>) {
          return crane_convert<T>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      if (std::holds_alternative<typename Exp0<_U>::ESELF>(_other.v())) {
        const auto &[a0] = std::get<typename Exp0<_U>::ESELF>(_other.v());
        this->v_ = ESELF{(a0 ? std::make_shared<Exp0<T>>(*a0) : nullptr)};
      } else {
        const auto &[a0] = std::get<typename Exp0<_U>::ENEG>(_other.v());
        this->v_ =
            ENEG{(a0 ? std::make_shared<std::pair<T, Exp0<T>>>(*a0) : nullptr)};
      }
    }
  }

  static Exp0<T> ev(T a0) { return Exp0<T>(EV{std::move(a0)}); }

  static Exp0<T> eself(Exp0<T> a0) {
    return Exp0<T>(ESELF{std::make_shared<Exp0<T>>(std::move(a0))});
  }

  static Exp0<T> eneg(std::pair<T, Exp0<T>> a0) {
    return Exp0<T>(
        ENEG{std::make_shared<std::pair<T, Exp0<T>>>(std::move(a0))});
  }

  // MANIPULATORS
  ~Exp0() {
    crane::small_vector<std::shared_ptr<Exp0<T>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<ESELF>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
      if (auto *_alt = std::get_if<ENEG>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _stack.push_back(
              std::make_shared<Exp0<T>>(std::move(_alt->a0->second)));
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

  Exp0(const Exp0 &) = default;
  Exp0 &operator=(const Exp0 &) = default;
  Exp0(Exp0 &&) noexcept = default;
  Exp0 &operator=(Exp0 &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat depth() const {
    if (std::holds_alternative<typename Exp0<T>::EV>(this->v())) {
      return Nat::s(Nat::o());
    } else if (std::holds_alternative<typename Exp0<T>::ESELF>(this->v())) {
      return Nat::s(Nat::s(Nat::o()));
    } else {
      return Nat::s(Nat::s(Nat::s(Nat::o())));
    }
  }

  Nat run() const { return this->depth(); }
};

#endif // INCLUDED_BOXED_PAIR_FIELD_CONV_CTOR
