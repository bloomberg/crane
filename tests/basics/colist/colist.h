#ifndef INCLUDED_COLIST
#define INCLUDED_COLIST

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

struct Colist {
  template <typename A> struct colist {
    // TYPES
    struct conil {};

    struct cocons {
      A _a0;
      std::shared_ptr<colist<A>> _a1;
    };

    using variant_t = std::variant<conil, cocons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

    // CREATORS
    explicit colist(conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<colist<A>> conil_() {
        return std::shared_ptr<colist<A>>(new colist<A>(conil{}));
      }

      static std::shared_ptr<colist<A>>
      cocons_(A a0, const std::shared_ptr<colist<A>> &a1) {
        return std::shared_ptr<colist<A>>(new colist<A>(cocons{a0, a1}));
      }

      static std::unique_ptr<colist<A>> conil_uptr() {
        return std::unique_ptr<colist<A>>(new colist<A>(conil{}));
      }

      static std::unique_ptr<colist<A>>
      cocons_uptr(A a0, const std::shared_ptr<colist<A>> &a1) {
        return std::unique_ptr<colist<A>>(new colist<A>(cocons{a0, a1}));
      }

      static std::shared_ptr<colist<A>>
      lazy_(std::function<std::shared_ptr<colist<A>>()> thunk) {
        return std::shared_ptr<colist<A>>(new colist<A>(
            std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<colist<A>> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    std::shared_ptr<List<A>>
    list_of_colist(const std::shared_ptr<Nat> &fuel) const {
      return std::visit(
          Overloaded{
              [](const typename Nat::O _args) -> std::shared_ptr<List<A>> {
                return List<A>::ctor::nil_();
              },
              [&](const typename Nat::S _args) -> std::shared_ptr<List<A>> {
                std::shared_ptr<Nat> fuel_ = _args._a0;
                return std::visit(
                    Overloaded{[](const typename colist<A>::conil _args)
                                   -> std::shared_ptr<List<A>> {
                                 return List<A>::ctor::nil_();
                               },
                               [&](const typename colist<A>::cocons _args)
                                   -> std::shared_ptr<List<A>> {
                                 A x = _args._a0;
                                 std::shared_ptr<colist<A>> xs = _args._a1;
                                 return List<A>::ctor::cons_(
                                     x, xs->list_of_colist(std::move(fuel_)));
                               }},
                    this->v());
              }},
          fuel->v());
    }

    template <typename T1, MapsTo<T1, A> F0>
    std::shared_ptr<colist<T1>> comap(F0 &&f) const {
      return colist<T1>::ctor::lazy_([=, this](
                                         void) -> std::shared_ptr<colist<T1>> {
        return std::visit(Overloaded{[](const typename colist<A>::conil _args)
                                         -> std::shared_ptr<colist<T1>> {
                                       return colist<T1>::ctor::conil_();
                                     },
                                     [&](const typename colist<A>::cocons _args)
                                         -> std::shared_ptr<colist<T1>> {
                                       A x = _args._a0;
                                       std::shared_ptr<colist<A>> xs =
                                           _args._a1;
                                       return colist<T1>::ctor::cocons_(
                                           f(x), xs->template comap<T1>(f));
                                     }},
                          this->v());
      });
    }
  };

  static std::shared_ptr<colist<std::shared_ptr<Nat>>>
  nats(std::shared_ptr<Nat> n);

  static inline const std::shared_ptr<List<std::shared_ptr<Nat>>> first_three =
      nats(Nat::ctor::O_())
          ->list_of_colist(
              Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))));
};

#endif // INCLUDED_COLIST
