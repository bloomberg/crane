#ifndef INCLUDED_STREAM
#define INCLUDED_STREAM

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

  static std::shared_ptr<Stream<t_A>>
  scons(t_A a0, const std::shared_ptr<Stream<t_A>> &a1) {
    return std::make_shared<Stream<t_A>>(Scons{std::move(a0), a1});
  }

  static std::shared_ptr<Stream<t_A>> scons(t_A a0,
                                            std::shared_ptr<Stream<t_A>> &&a1) {
    return std::make_shared<Stream<t_A>>(Scons{std::move(a0), std::move(a1)});
  }

  static std::shared_ptr<Stream<t_A>>
  lazy_(std::function<std::shared_ptr<Stream<t_A>>()> thunk) {
    return std::make_shared<Stream<t_A>>(
        std::function<variant_t()>([=]() mutable -> variant_t {
          std::shared_ptr<Stream<t_A>> _tmp = thunk();
          return _tmp->v();
        }));
  }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_lazyV_.force(); }

  std::shared_ptr<List<t_A>> take(const std::shared_ptr<Nat> &n) const {
    if (std::holds_alternative<typename Nat::O>(n->v())) {
      return List<t_A>::nil();
    } else {
      const auto &_m = *std::get_if<typename Nat::S>(&n->v());
      const auto &_m0 = *std::get_if<typename Stream<t_A>::Scons>(&this->v());
      return List<t_A>::cons(_m0.d_a0, _m0.d_a1->take(_m.d_a0));
    }
  }

  std::shared_ptr<Stream<t_A>>
  interleave(const std::shared_ptr<Stream<t_A>> &sb) const {
    const auto &_m = *std::get_if<typename Stream<t_A>::Scons>(&this->v());
    return Stream<t_A>::lazy_([=]() mutable -> std::shared_ptr<Stream<t_A>> {
      return Stream<t_A>::scons(_m.d_a0, sb->interleave(_m.d_a1));
    });
  }

  template <typename T1> static std::shared_ptr<Stream<T1>> repeat(const T1 x) {
    return Stream<T1>::lazy_([=]() mutable -> std::shared_ptr<Stream<T1>> {
      return Stream<T1>::scons(x, repeat<T1>(x));
    });
  }

  static std::shared_ptr<Stream<std::shared_ptr<Nat>>>
  nats_from(std::shared_ptr<Nat> n) {
    return Stream<std::shared_ptr<Nat>>::lazy_(
        [=]() mutable -> std::shared_ptr<Stream<std::shared_ptr<Nat>>> {
          return Stream<std::shared_ptr<Nat>>::scons(n, nats_from(Nat::s(n)));
        });
  }

  static const std::shared_ptr<Stream<std::shared_ptr<Nat>>> &ones() {
    static const std::shared_ptr<Stream<std::shared_ptr<Nat>>> v =
        repeat<std::shared_ptr<Nat>>(Nat::s(Nat::o()));
    return v;
  }

  static const std::shared_ptr<List<std::shared_ptr<Nat>>> &first_five_nats() {
    static const std::shared_ptr<List<std::shared_ptr<Nat>>> v =
        nats_from(Nat::o())->take(
            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));
    return v;
  }

  static const std::shared_ptr<List<std::shared_ptr<Nat>>> &first_five_ones() {
    static const std::shared_ptr<List<std::shared_ptr<Nat>>> v =
        ones()->take(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));
    return v;
  }

  static const std::shared_ptr<List<std::shared_ptr<Nat>>> &interleaved() {
    static const std::shared_ptr<List<std::shared_ptr<Nat>>> v =
        nats_from(Nat::o())
            ->interleave(repeat<std::shared_ptr<Nat>>(Nat::s(
                Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))))
            ->take(Nat::s(Nat::s(
                Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))));
    return v;
  }
};

#endif // INCLUDED_STREAM
