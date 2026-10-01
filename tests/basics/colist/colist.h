#ifndef INCLUDED_COLIST
#define INCLUDED_COLIST

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
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
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
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

template <typename A> struct Colist {
  // TYPES
  struct Conil {};

  template <typename _S0 = Colist<A>> struct Cocons_ {
    A x;
    _S0 xs;
  };

  using Cocons = Cocons_<>;
  using variant_t = std::variant<Conil, Cocons>;

private:
  // DATA
  crane::lazy<variant_t> lazy_v_;

public:
  // CREATORS
  Colist() {}

  explicit Colist(Conil _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Colist(Cocons _v)
      : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  template <typename _U>
  Colist(const Colist<_U> &_other)
      : lazy_v_(crane::lazy<variant_t>::converted_from(
            _other.lazy_cell(), [=]() -> variant_t {
              if (std::holds_alternative<typename Colist<_U>::Conil>(
                      _other.v())) {
                return Conil{};
              } else {
                const auto &[x, xs] =
                    std::get<typename Colist<_U>::Cocons>(_other.v());
                return Cocons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const _U &>) {
                        return crane_convert<A>(x);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    crane_convert<Colist<A>>(xs)};
              }
            })) {}

  explicit Colist(crane::fn<variant_t()> _thunk)
      : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static Colist<A> conil() { return Colist<A>(Conil{}); }

  static Colist<A> cocons(A x, Colist<A> xs) {
    return Colist<A>(Cocons{std::move(x), std::move(xs)});
  }

  explicit Colist(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

  template <typename F> static Colist<A> lazy_(F &&thunk) {
    return Colist<A>(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
  }

  // ACCESSORS
  const variant_t &v() const { return lazy_v_.force(); }

  const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  Colist<T1> comap(F0 &&f) const {
    if (std::holds_alternative<typename Colist<A>::Conil>(this->v())) {
      return Colist<T1>::conil();
    } else {
      const auto &[a0, a1] = std::get<typename Colist<A>::Cocons>(this->v());
      return Colist<T1>::lazy_([=]() -> Colist<T1> {
        return Colist<T1>::cocons(f(a0), a1.template comap<T1>(f));
      });
    }
  }

  template <typename T1>
  static List<T1> list_of_colist(const Nat &fuel, Colist<T1> l) {
    if (std::holds_alternative<typename Nat::O>(fuel.v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0] = std::get<typename Nat::S>(fuel.v());
      if (std::holds_alternative<typename Colist<T1>::Conil>(l.v())) {
        return List<T1>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename Colist<T1>::Cocons>(l.v());
        return List<T1>::cons(a00, list_of_colist<T1>(*a0, a10));
      }
    }
  }

  static Colist<Nat> nats(const Nat &n) {
    return Colist<Nat>::lazy_([=]() -> Colist<Nat> {
      return Colist<Nat>::cocons(n, nats(Nat::s(n)));
    });
  }

  static const List<Nat> &first_three() {
    static const List<Nat> v =
        list_of_colist<Nat>(Nat::s(Nat::s(Nat::s(Nat::o()))), nats(Nat::o()));
    return v;
  }
};

#endif // INCLUDED_COLIST
