#ifndef INCLUDED_ITREE_MAPPING_HIJACKS_MONAD
#define INCLUDED_ITREE_MAPPING_HIJACKS_MONAD

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename X> struct Err;
struct Monad_Err;

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

template <typename I>
concept Monad = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

template <typename X> struct Err {
  // TYPES
  struct Ok {
    X x;
  };

  struct Bad {};

  using variant_t = std::variant<Ok, Bad>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Err() {}

  explicit Err(Ok _v) : v_(std::move(_v)) {}

  explicit Err(Bad _v) : v_(_v) {}

  template <typename _U> Err(const Err<_U> &_other) {
    if (std::holds_alternative<typename Err<_U>::Ok>(_other.v())) {
      const auto &[x] = std::get<typename Err<_U>::Ok>(_other.v());
      this->v_ = Ok{[&]() -> X {
        if constexpr (std::is_same_v<_U, std::any>) {
          return crane_any_cast<X>(x);
        } else {
          return X(x);
        }
      }()};
    } else {
      this->v_ = Bad{};
    }
  }

  static Err<X> ok(X x) { return Err<X>(Ok{std::move(x)}); }

  static Err<X> bad() { return Err<X>(Bad{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Monad_Err {
  template <typename _A0> using m = Err<_A0>;

  template <typename _A0> static Err<_A0> ret(_A0 x) {
    return Err<_A0>::ok(std::move(x));
  }

  template <typename _A0, typename _A1>
  static Err<_A1> bind(Err<_A0> c, std::function<Err<_A1>(_A0)> k) {
    if (std::holds_alternative<typename Err<_A0>::Ok>(c.v())) {
      const auto &[x0] = std::get<typename Err<_A0>::Ok>(c.v());
      return std::move(k)(x0);
    } else {
      return Err<_A1>::bad();
    }
  }
};

static_assert(Monad<Monad_Err>);
Err<Nat> twice(const Err<Nat> &x);

struct ItreeMappingHijacksMonad {
  static Err<Nat> use(Nat n);
};

#endif // INCLUDED_ITREE_MAPPING_HIJACKS_MONAD
