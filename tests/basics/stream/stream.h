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
    std::shared_ptr<Nat> _a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Nat(O _v) : v_(std::move(_v)) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

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
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Stream {
  template <typename A> struct stream {
    // TYPES
    struct scons {
      A _a0;
      std::shared_ptr<stream<A>> _a1;
    };

    using variant_t = std::variant<scons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

    // CREATORS
    explicit stream(scons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<stream<A>>
      scons_(A a0, const std::shared_ptr<stream<A>> &a1) {
        return std::shared_ptr<stream<A>>(new stream<A>(scons{a0, a1}));
      }

      static std::unique_ptr<stream<A>>
      scons_uptr(A a0, const std::shared_ptr<stream<A>> &a1) {
        return std::unique_ptr<stream<A>>(new stream<A>(scons{a0, a1}));
      }

      static std::shared_ptr<stream<A>>
      lazy_(std::function<std::shared_ptr<stream<A>>()> thunk) {
        return std::shared_ptr<stream<A>>(new stream<A>(
            std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<stream<A>> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    std::shared_ptr<List<A>> take(const std::shared_ptr<Nat> &n) const {
      return std::visit(
          Overloaded{
              [](const typename Nat::O _args) -> std::shared_ptr<List<A>> {
                return List<A>::ctor::nil_();
              },
              [&](const typename Nat::S _args) -> std::shared_ptr<List<A>> {
                std::shared_ptr<Nat> n_ = _args._a0;
                return std::visit(
                    Overloaded{[&](const typename stream<A>::scons _args)
                                   -> std::shared_ptr<List<A>> {
                      A x = _args._a0;
                      std::shared_ptr<stream<A>> xs = _args._a1;
                      return List<A>::ctor::cons_(x, xs->take(std::move(n_)));
                    }},
                    this->v());
              }},
          n->v());
    }

    std::shared_ptr<stream<A>> interleave(std::shared_ptr<stream<A>> sb) const {
      return stream<A>::ctor::lazy_([=,
                                     this](void) -> std::shared_ptr<stream<A>> {
        return std::visit(Overloaded{[&](const typename stream<A>::scons _args)
                                         -> std::shared_ptr<stream<A>> {
                            A a = _args._a0;
                            std::shared_ptr<stream<A>> as_ = _args._a1;
                            return stream<A>::ctor::scons_(a,
                                                           sb->interleave(as_));
                          }},
                          this->v());
      });
    }
  };

  template <typename T1> static std::shared_ptr<stream<T1>> repeat(const T1 x) {
    return stream<T1>::ctor::lazy_(
        [=](void) mutable -> std::shared_ptr<stream<T1>> {
          return stream<T1>::ctor::scons_(x, repeat<T1>(x));
        });
  }

  static std::shared_ptr<stream<std::shared_ptr<Nat>>>
  nats_from(std::shared_ptr<Nat> n);
  static inline const std::shared_ptr<stream<std::shared_ptr<Nat>>> ones =
      repeat<std::shared_ptr<Nat>>(Nat::ctor::S_(Nat::ctor::O_()));
  static inline const std::shared_ptr<List<std::shared_ptr<Nat>>>
      first_five_nats =
          nats_from(Nat::ctor::O_())
              ->take(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))));
  static inline const std::shared_ptr<List<std::shared_ptr<Nat>>>
      first_five_ones = ones->take(Nat::ctor::S_(Nat::ctor::S_(
          Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))));
  static inline const std::shared_ptr<List<std::shared_ptr<Nat>>> interleaved =
      nats_from(Nat::ctor::O_())
          ->interleave(repeat<std::shared_ptr<Nat>>(Nat::ctor::S_(
              Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))))))))
          ->take(Nat::ctor::S_(Nat::ctor::S_(
              Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())))))))));
};
