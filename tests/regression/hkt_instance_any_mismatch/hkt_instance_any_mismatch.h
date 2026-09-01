#ifndef INCLUDED_HKT_INSTANCE_ANY_MISMATCH
#define INCLUDED_HKT_INSTANCE_ANY_MISMATCH

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct Option;

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

template <typename A> struct Option {
  // TYPES
  struct Some {
    A a;
  };

  struct None {};

  using variant_t = std::variant<Some, None>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Option() {}

  explicit Option(Some _v) : v_(std::move(_v)) {}

  explicit Option(None _v) : v_(_v) {}

  template <typename _U> Option(const Option<_U> &_other) {
    if (std::holds_alternative<typename Option<_U>::Some>(_other.v())) {
      const auto &[a] = std::get<typename Option<_U>::Some>(_other.v());
      this->v_ = Some{[&]() -> A {
        if constexpr (std::is_same_v<_U, std::any>) {
          if (a.type() == typeid(A))
            return std::any_cast<A>(a);
          if constexpr (requires {
                          typename A::first_type;
                          typename A::second_type;
                        }) {
            const auto &[_k, _v] =
                std::any_cast<std::pair<std::any, std::any>>(a);
            return A{[&]() -> typename A::first_type {
                       if constexpr (std::is_same_v<typename A::first_type,
                                                    std::any>)
                         return _k;
                       else
                         return std::any_cast<typename A::first_type>(_k);
                     }(),
                     [&]() -> typename A::second_type {
                       if constexpr (std::is_same_v<typename A::second_type,
                                                    std::any>)
                         return _v;
                       else
                         return std::any_cast<typename A::second_type>(_v);
                     }()};
          }
          return std::any_cast<A>(a);
        } else
          return A(a);
      }()};
    } else {
      this->v_ = None{};
    }
  }

  static Option<A> some(A a) { return Option<A>(Some{std::move(a)}); }

  static Option<A> none() { return Option<A>(None{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I>
concept Mon = requires {
  typename I::template M<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template M<std::any>>;
  {
    I::template bind<std::any, std::any>(
        std::declval<typename I::template M<std::any>>(),
        std::declval<
            std::function<typename I::template M<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template M<std::any>>;
};

struct HktInstanceAnyMismatch {
  template <Mon _tcI0, typename T2>
  static typename _tcI0::template M<T2> ret(const T2 &x) {
    return _tcI0::template ret<T2>(x);
  }

  template <Mon _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template M<T3>, F1 &, T2 &>
  static typename _tcI0::template M<T3> bind(typename _tcI0::template M<T2> x,
                                             F1 &&x0) {
    return _tcI0::template bind<T2, T3>(x, x0);
  }

  struct optMon {
    template <typename _A0> using M = Option<_A0>;

    template <typename _A0> static Option<_A0> ret(_A0 a) {
      return Option<_A0>::some(a);
    }

    template <typename _A0, typename _A1>
    static Option<_A1> bind(Option<_A0> m, std::function<Option<_A1>(_A0)> f) {
      if (std::holds_alternative<typename Option<_A0>::Some>(m.v())) {
        const auto &[a0] = std::get<typename Option<_A0>::Some>(m.v());
        return f(a0);
      } else {
        return Option<_A1>::none();
      }
    }
  };

  static_assert(Mon<optMon>);
  static inline const Option<Nat> test =
      bind<optMon, Nat, Nat>(ret<optMon, Nat>(Nat::s(Nat::o())),
                             [](Nat n) { return ret<optMon, Nat>(Nat::s(n)); });
};

#endif // INCLUDED_HKT_INSTANCE_ANY_MISMATCH
