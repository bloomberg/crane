#ifndef INCLUDED_INSTANCE_USED_BEFORE_DEFINED
#define INCLUDED_INSTANCE_USED_BEFORE_DEFINED

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct EOU_monad;
struct Nat;
template <typename X> struct EOU;
template <typename I> struct Arith;

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
    I::bind(std::declval<typename I::template m<std::any>>(),
            std::declval<
                std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
};

template <typename X> struct EOU {
  // TYPES
  struct Raise_error {
    Nat s;
  };

  struct Raise_ret {
    X x;
  };

  using variant_t = std::variant<Raise_error, Raise_ret>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Raise_error _v) : v_(std::move(_v)) {}

  explicit EOU(Raise_ret _v) : v_(std::move(_v)) {}

  template <typename _U> EOU(const EOU<_U> &_other) {
    if (std::holds_alternative<typename EOU<_U>::Raise_error>(_other.v())) {
      const auto &[s] = std::get<typename EOU<_U>::Raise_error>(_other.v());
      this->v_ = Raise_error{s};
    } else {
      const auto &[x] = std::get<typename EOU<_U>::Raise_ret>(_other.v());
      this->v_ = Raise_ret{[&]() -> X {
        if constexpr (std::is_same_v<_U, std::any>) {
          return crane_any_cast<X>(x);
        } else {
          if constexpr (std::is_constructible_v<X, const _U &>) {
            return X(x);
          } else {
            throw std::logic_error("unreachable: inactive constructor field at "
                                   "this instantiation");
          }
        }
      }()};
    }
  }

  static EOU<X> raise_error(Nat s) { return EOU<X>(Raise_error{std::move(s)}); }

  static EOU<X> raise_ret(X x) { return EOU<X>(Raise_ret{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU_monad {
  template <typename _A0> using m = EOU<_A0>;

  template <typename _A0> static EOU<_A0> ret(_A0 x) {
    return EOU<_A0>::raise_ret(std::move(x));
  }

  static EOU<std::any> bind(EOU<std::any> c,
                            std::function<EOU<std::any>(std::any)> k) {
    if (std::holds_alternative<typename EOU<std::any>::Raise_error>(c.v())) {
      const auto &[s0] = std::get<typename EOU<std::any>::Raise_error>(c.v());
      return EOU<std::any>::raise_error(s0);
    } else {
      const auto &[x0] = std::get<typename EOU<std::any>::Raise_ret>(c.v());
      return k(x0);
    }
  }
};

static_assert(Monad<EOU_monad>);

template <typename I> struct Arith {
  std::function<EOU<I>(I, I)> madd;
  I mzero;
};

struct Ops {
  static inline const Arith<Nat> Arith_nat =
      Arith<Nat>{[](const Nat &x, const Nat &y) {
                   return Monad0::template ret<EOU_monad, Nat>(x.add(y));
                 },
                 Nat::o()};
};

struct InstanceUsedBeforeDefined {
  static EOU<Nat> use(const Nat &n);
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

#endif // INCLUDED_INSTANCE_USED_BEFORE_DEFINED
