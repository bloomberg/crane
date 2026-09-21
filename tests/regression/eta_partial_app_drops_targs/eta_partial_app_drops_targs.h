#ifndef INCLUDED_ETA_PARTIAL_APP_DROPS_TARGS
#define INCLUDED_ETA_PARTIAL_APP_DROPS_TARGS

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct Mon_option;

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

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(a);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                  : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I>
concept Mon = requires {
  typename I::template m<std::any>;
  {
    I::template mret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template mbind<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

template <Mon _tcI0, typename T2>
typename _tcI0::template m<T2> mret(const T2 &x) {
  return _tcI0::template mret<T2>(x);
}

template <Mon _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
typename _tcI0::template m<T3> mbind(typename _tcI0::template m<T2> x,
                                     F1 &&x0) {
  return _tcI0::template mbind<T2, T3>(std::move(x), x0);
}

template <Mon _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<T3, F0 &, T2 &>
typename _tcI0::template m<T3> liftM(F0 &&f, typename _tcI0::template m<T2> x) {
  return mbind<_tcI0, T2, T3>(
      std::move(x), [=](const T2 &a) mutable { return mret<_tcI0, T3>(f(a)); });
}

template <typename I>
concept Fun = requires {
  typename I::template F<std::any>;
  {
    I::template ffmap<std::any, std::any>(
        std::declval<std::function<std::any(std::any)>>(),
        std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
  {
    I::fconst(std::declval<std::any>(),
              std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
};

template <Fun _tcI0, typename T2, typename T3, typename F0>
  requires std::is_invocable_r_v<T3, F0 &, T2 &>
typename _tcI0::template F<T3> ffmap(F0 &&x,
                                     typename _tcI0::template F<T2> x0) {
  return _tcI0::template ffmap<T2, T3>(x, std::move(x0));
}

struct Mon_option {
  template <typename _A0> using m = std::optional<_A0>;

  template <typename _A0> static std::optional<_A0> mret(_A0 a) {
    return std::make_optional<_A0>(a);
  }

  template <typename _A0, typename _A1>
  static std::optional<_A1> mbind(std::optional<_A0> o,
                                  std::function<std::optional<_A1>(_A0)> k) {
    if (o.has_value()) {
      const _A0 &a = *o;
      return k(a);
    } else {
      return std::optional<_A1>();
    }
  }
};

static_assert(Mon<Mon_option>);

template <Mon _tcI0> struct Fun_Mon {
  template <typename _A0> using m = typename _tcI0::template m<_A0>;
  template <typename _A0> using F = typename _tcI0::template m<_A0>;

  template <typename _A0, typename _A1>
  static typename _tcI0::template m<_A1>
  ffmap(std::function<_A1(_A0)> a0, typename _tcI0::template m<_A0> a1) {
    return liftM<_tcI0, _A0, _A1>(std::move(a0), std::move(a1));
  }

  static typename _tcI0::template m<std::any> fconst(std::any a, std::any x) {
    return liftM<_tcI0, std::any, std::any>(
        [=](const auto &) mutable { return a; }, x);
  }
};

std::optional<List<Nat>> run(const std::optional<Nat> &o);

#endif // INCLUDED_ETA_PARTIAL_APP_DROPS_TARGS
