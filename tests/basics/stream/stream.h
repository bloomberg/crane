#ifndef INCLUDED_STREAM
#define INCLUDED_STREAM

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

  Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
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

  __attribute__((pure)) static Nat s(Nat a0) {
    return Nat(S{std::make_unique<Nat>(std::move(a0))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
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

  __attribute__((pure)) static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Stream {
  // TYPES
  struct Scons {
    t_A d_a0;
    std::shared_ptr<Stream<t_A>> d_a1;
  };

  using variant_t = std::variant<Scons>;

private:
  // DATA
  crane::lazy<variant_t> d_lazyV_;

public:
  // CREATORS
  explicit Stream(Scons _v)
      : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Stream(std::function<variant_t()> _thunk)
      : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  __attribute__((pure)) static Stream<t_A> scons(t_A a0,
                                                 const Stream<t_A> &a1) {
    return Stream(Scons{std::move(a0), std::make_shared<Stream<t_A>>(a1)});
  }

  __attribute__((pure)) static Stream<t_A>
  lazy_(std::function<Stream<t_A>()> thunk) {
    return Stream<t_A>(std::function<variant_t()>([=]() mutable -> variant_t {
      Stream<t_A> _tmp = thunk();
      return _tmp.v();
    }));
  }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_lazyV_.force(); }

  __attribute__((pure)) Stream<t_A> interleave(const Stream<t_A> sb) const {
    const auto &[d_a0, d_a1] = std::get<typename Stream<t_A>::Scons>(this->v());
    return Stream<t_A>::lazy_([=]() mutable -> Stream<t_A> {
      return Stream<t_A>::scons(d_a0, sb.interleave(*(d_a1)));
    });
  }

  template <typename T1>
  __attribute__((pure)) static List<T1> take(const Nat &n, const Stream<T1> s) {
    if (std::holds_alternative<typename Nat::O>(n.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(n.v());
      const auto &[d_a00, d_a10] = std::get<typename Stream<T1>::Scons>(s.v());
      return List<T1>::cons(d_a00, take<T1>(*(d_a0), *(d_a10)));
    }
  }

  template <typename T1>
  __attribute__((pure)) static Stream<T1> repeat(const T1 x) {
    return Stream<T1>::lazy_([=]() mutable -> Stream<T1> {
      return Stream<T1>::scons(x, repeat<T1>(x));
    });
  }

  __attribute__((pure)) static Stream<Nat> nats_from(Nat n) {
    return Stream<Nat>::lazy_([=]() mutable -> Stream<Nat> {
      return Stream<Nat>::scons(n, nats_from(Nat::s(n)));
    });
  }

  static const Stream<Nat> &ones() {
    static const Stream<Nat> v = repeat<Nat>(Nat::s(Nat::o()));
    return v;
  }

  static const List<Nat> &first_five_nats() {
    static const List<Nat> v = take<Nat>(
        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))), nats_from(Nat::o()));
    return v;
  }

  static const List<Nat> &first_five_ones() {
    static const List<Nat> v =
        take<Nat>(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))), ones());
    return v;
  }

  static const List<Nat> &interleaved() {
    static const List<Nat> v = take<Nat>(
        Nat::s(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))),
        nats_from(Nat::o()).interleave(repeat<Nat>(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))));
    return v;
  }
};

#endif // INCLUDED_STREAM
