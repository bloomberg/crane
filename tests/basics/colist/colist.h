#ifndef INCLUDED_COLIST
#define INCLUDED_COLIST

#include "lazy.h"
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Colist {
  // TYPES
  struct Conil {};

  struct Cocons {
    t_A d_a0;
    std::shared_ptr<Colist<t_A>> d_a1;
  };

  using variant_t = std::variant<Conil, Cocons>;

private:
  // DATA
  crane::lazy<variant_t> d_lazyV_;

public:
  // CREATORS
  explicit Colist(Conil _v)
      : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Colist(Cocons _v)
      : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Colist(std::function<variant_t()> _thunk)
      : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  static std::shared_ptr<Colist<t_A>> conil() {
    return std::make_shared<Colist<t_A>>(Conil{});
  }

  static std::shared_ptr<Colist<t_A>>
  cocons(t_A a0, const std::shared_ptr<Colist<t_A>> &a1) {
    return std::make_shared<Colist<t_A>>(Cocons{std::move(a0), a1});
  }

  static std::shared_ptr<Colist<t_A>>
  cocons(t_A a0, std::shared_ptr<Colist<t_A>> &&a1) {
    return std::make_shared<Colist<t_A>>(Cocons{std::move(a0), std::move(a1)});
  }

  static std::shared_ptr<Colist<t_A>>
  lazy_(std::function<std::shared_ptr<Colist<t_A>>()> thunk) {
    return std::make_shared<Colist<t_A>>(
        std::function<variant_t()>([=]() mutable -> variant_t {
          std::shared_ptr<Colist<t_A>> _tmp = thunk();
          return _tmp->v();
        }));
  }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_lazyV_.force(); }

  template <typename T1, MapsTo<T1, t_A> F0>
  std::shared_ptr<Colist<T1>> comap(F0 &&f) const {
    if (std::holds_alternative<typename Colist<t_A>::Conil>(this->v())) {
      return Colist<T1>::lazy_(
          []() -> std::shared_ptr<Colist<T1>> { return Colist<T1>::conil(); });
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename Colist<t_A>::Cocons>(this->v());
      return Colist<T1>::lazy_([=]() mutable -> std::shared_ptr<Colist<T1>> {
        return Colist<T1>::cocons(f(d_a0), d_a1->template comap<T1>(f));
      });
    }
  }

  template <typename T1>
  static std::shared_ptr<List<T1>>
  list_of_colist(const std::shared_ptr<Nat> &fuel,
                 const std::shared_ptr<Colist<T1>> &l) {
    if (std::holds_alternative<typename Nat::O>(fuel->v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(fuel->v());
      if (std::holds_alternative<typename Colist<T1>::Conil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename Colist<T1>::Cocons>(l->v());
        return List<T1>::cons(d_a00, list_of_colist<T1>(d_a0, d_a10));
      }
    }
  }

  static std::shared_ptr<Colist<std::shared_ptr<Nat>>>
  nats(std::shared_ptr<Nat> n) {
    return Colist<std::shared_ptr<Nat>>::lazy_(
        [=]() mutable -> std::shared_ptr<Colist<std::shared_ptr<Nat>>> {
          return Colist<std::shared_ptr<Nat>>::cocons(n, nats(Nat::s(n)));
        });
  }

  static const std::shared_ptr<List<std::shared_ptr<Nat>>> &first_three() {
    static const std::shared_ptr<List<std::shared_ptr<Nat>>> v =
        list_of_colist<std::shared_ptr<Nat>>(Nat::s(Nat::s(Nat::s(Nat::o()))),
                                             nats(Nat::o()));
    return v;
  }
};

#endif // INCLUDED_COLIST
