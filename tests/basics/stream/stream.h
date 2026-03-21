#ifndef INCLUDED_STREAM
#define INCLUDED_STREAM

#include "lazy.h"
#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

  // CREATORS
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Nat> O_() {
      return std::shared_ptr<Nat>(new Nat(O{}));
    }

    static std::shared_ptr<Nat> S_(const std::shared_ptr<Nat> &a0) {
      return std::shared_ptr<Nat>(new Nat(S{a0}));
    }

    static std::unique_ptr<Nat> O_uptr() {
      return std::unique_ptr<Nat>(new Nat(O{}));
    }

    static std::unique_ptr<Nat> S_uptr(const std::shared_ptr<Nat> &a0) {
      return std::unique_ptr<Nat>(new Nat(S{a0}));
    }
  };

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

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

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

  // CREATORS
  explicit Stream(Scons _v)
      : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

  explicit Stream(std::function<variant_t()> _thunk)
      : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Stream<t_A>>
    Scons_(t_A a0, const std::shared_ptr<Stream<t_A>> &a1) {
      return std::shared_ptr<Stream<t_A>>(new Stream<t_A>(Scons{a0, a1}));
    }

    static std::unique_ptr<Stream<t_A>>
    Scons_uptr(t_A a0, const std::shared_ptr<Stream<t_A>> &a1) {
      return std::unique_ptr<Stream<t_A>>(new Stream<t_A>(Scons{a0, a1}));
    }

    static std::shared_ptr<Stream<t_A>>
    lazy_(std::function<std::shared_ptr<Stream<t_A>>()> thunk) {
      return std::shared_ptr<Stream<t_A>>(new Stream<t_A>(
          std::function<variant_t()>([=](void) mutable -> variant_t {
            std::shared_ptr<Stream<t_A>> _tmp = thunk();
            return _tmp->v();
          })));
    }
  };

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_lazyV_.force(); }

  std::shared_ptr<List<t_A>> take(const std::shared_ptr<Nat> &n) const {
    return std::visit(
        Overloaded{
            [](const typename Nat::O _args) -> std::shared_ptr<List<t_A>> {
              return List<t_A>::ctor::Nil_();
            },
            [&](const typename Nat::S _args) -> std::shared_ptr<List<t_A>> {
              return std::visit(
                  Overloaded{[&](const typename Stream<t_A>::Scons _args0)
                                 -> std::shared_ptr<List<t_A>> {
                    return List<t_A>::ctor::Cons_(
                        _args0.d_a0, _args0.d_a1->take(_args.d_a0));
                  }},
                  this->v());
            }},
        n->v());
  }

  std::shared_ptr<Stream<t_A>>
  interleave(std::shared_ptr<Stream<t_A>> sb) const {
    return Stream<t_A>::ctor::lazy_([=, this](
                                        void) -> std::shared_ptr<Stream<t_A>> {
      return std::visit(Overloaded{[&](const typename Stream<t_A>::Scons _args)
                                       -> std::shared_ptr<Stream<t_A>> {
                          return Stream<t_A>::ctor::Scons_(
                              _args.d_a0, sb->interleave(_args.d_a1));
                        }},
                        this->v());
    });
  }

  template <typename T1> static std::shared_ptr<Stream<T1>> repeat(const T1 x) {
    return Stream<T1>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<Stream<T1>> {
          return Stream<T1>::ctor::Scons_(x, repeat<T1>(x));
        });
  }

  static std::shared_ptr<Stream<std::shared_ptr<Nat>>>
  nats_from(std::shared_ptr<Nat> n) {
    return Stream<std::shared_ptr<Nat>>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<Stream<std::shared_ptr<Nat>>> {
          return Stream<std::shared_ptr<Nat>>::ctor::Scons_(
              n, nats_from(Nat::ctor::S_(n)));
        });
  }

  static const std::shared_ptr<Stream<std::shared_ptr<Nat>>> &ones() {
    static const std::shared_ptr<Stream<std::shared_ptr<Nat>>> v =
        repeat<std::shared_ptr<Nat>>(Nat::ctor::S_(Nat::ctor::O_()));
    return v;
  }

  static const std::shared_ptr<List<std::shared_ptr<Nat>>> &first_five_nats() {
    static const std::shared_ptr<List<std::shared_ptr<Nat>>> v =
        nats_from(Nat::ctor::O_())
            ->take(Nat::ctor::S_(Nat::ctor::S_(
                Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))));
    return v;
  }

  static const std::shared_ptr<List<std::shared_ptr<Nat>>> &first_five_ones() {
    static const std::shared_ptr<List<std::shared_ptr<Nat>>> v =
        ones()->take(Nat::ctor::S_(Nat::ctor::S_(
            Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))));
    return v;
  }

  static const std::shared_ptr<List<std::shared_ptr<Nat>>> &interleaved() {
    static const std::shared_ptr<List<std::shared_ptr<Nat>>> v =
        nats_from(Nat::ctor::O_())
            ->interleave(repeat<std::shared_ptr<Nat>>(Nat::ctor::S_(
                Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                    Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))))))))
            ->take(Nat::ctor::S_(Nat::ctor::S_(
                Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                    Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))))))));
    return v;
  }
};

#endif // INCLUDED_STREAM
