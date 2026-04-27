#ifndef INCLUDED_COLIST
#define INCLUDED_COLIST

#include "lazy.h"
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Nat clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<O>(_sv.v())) {
      return Nat(O{});
    } else {
      const auto &[d_a0] = std::get<S>(_sv.v());
      return Nat(S{d_a0 ? std::make_unique<Nat>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Nat o() { return Nat(O{}); }

  __attribute__((pure)) static Nat s(const Nat &a0) {
    return Nat(S{std::make_unique<Nat>(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Nat *operator->() { return this; }

  __attribute__((pure)) const Nat *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Nat(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

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
  using crane_element_type = t_A;

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

  static std::shared_ptr<Colist<t_A>> cocons(t_A a0,
                                             std::shared_ptr<Colist<t_A>> a1) {
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
  __attribute__((pure)) static List<T1>
  list_of_colist(const Nat &fuel, const std::shared_ptr<Colist<T1>> &l) {
    if (std::holds_alternative<typename Nat::O>(fuel.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(fuel.v());
      if (std::holds_alternative<typename Colist<T1>::Conil>(l->v())) {
        return List<T1>::nil();
      } else {
        const auto &[d_a00, d_a10] =
            std::get<typename Colist<T1>::Cocons>(l->v());
        return List<T1>::cons(d_a00, list_of_colist<T1>(*(d_a0), d_a10));
      }
    }
  }

  static std::shared_ptr<Colist<Nat>> nats(Nat n) {
    return Colist<Nat>::lazy_([=]() mutable -> std::shared_ptr<Colist<Nat>> {
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
