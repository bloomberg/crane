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

struct Colist {
  template <typename t_A> struct colist {
    // TYPES
    struct Conil {};

    struct Cocons {
      t_A d_a0;
      std::shared_ptr<colist<t_A>> d_a1;
    };

    using variant_t = std::variant<Conil, Cocons>;

  private:
    // DATA
    crane::lazy<variant_t> d_lazyV_;

    // CREATORS
    explicit colist(Conil _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(Cocons _v)
        : d_lazyV_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit colist(std::function<variant_t()> _thunk)
        : d_lazyV_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<colist<t_A>> Conil_() {
        return std::shared_ptr<colist<t_A>>(new colist<t_A>(Conil{}));
      }

      static std::shared_ptr<colist<t_A>>
      Cocons_(t_A a0, const std::shared_ptr<colist<t_A>> &a1) {
        return std::shared_ptr<colist<t_A>>(new colist<t_A>(Cocons{a0, a1}));
      }

      static std::unique_ptr<colist<t_A>> Conil_uptr() {
        return std::unique_ptr<colist<t_A>>(new colist<t_A>(Conil{}));
      }

      static std::unique_ptr<colist<t_A>>
      Cocons_uptr(t_A a0, const std::shared_ptr<colist<t_A>> &a1) {
        return std::unique_ptr<colist<t_A>>(new colist<t_A>(Cocons{a0, a1}));
      }

      static std::shared_ptr<colist<t_A>>
      lazy_(std::function<std::shared_ptr<colist<t_A>>()> thunk) {
        return std::shared_ptr<colist<t_A>>(new colist<t_A>(
            std::function<variant_t()>([=](void) mutable -> variant_t {
              std::shared_ptr<colist<t_A>> _tmp = thunk();
              return _tmp->v();
            })));
      }
    };

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const {
      return d_lazyV_.force();
    }

    std::shared_ptr<List<t_A>>
    list_of_colist(const std::shared_ptr<Nat> &fuel) const {
      return std::visit(
          Overloaded{
              [](const typename Nat::O _args) -> std::shared_ptr<List<t_A>> {
                return List<t_A>::ctor::Nil_();
              },
              [&](const typename Nat::S _args) -> std::shared_ptr<List<t_A>> {
                std::shared_ptr<Nat> fuel_ = _args.d_a0;
                return std::visit(
                    Overloaded{[](const typename colist<t_A>::Conil _args)
                                   -> std::shared_ptr<List<t_A>> {
                                 return List<t_A>::ctor::Nil_();
                               },
                               [&](const typename colist<t_A>::Cocons _args)
                                   -> std::shared_ptr<List<t_A>> {
                                 t_A x = _args.d_a0;
                                 std::shared_ptr<colist<t_A>> xs = _args.d_a1;
                                 return List<t_A>::ctor::Cons_(
                                     x, xs->list_of_colist(std::move(fuel_)));
                               }},
                    this->v());
              }},
          fuel->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<colist<T1>> comap(F0 &&f) const {
      return colist<T1>::ctor::lazy_(
          [=, this](void) -> std::shared_ptr<colist<T1>> {
            return std::visit(
                Overloaded{[](const typename colist<t_A>::Conil _args)
                               -> std::shared_ptr<colist<T1>> {
                             return colist<T1>::ctor::Conil_();
                           },
                           [&](const typename colist<t_A>::Cocons _args)
                               -> std::shared_ptr<colist<T1>> {
                             t_A x = _args.d_a0;
                             std::shared_ptr<colist<t_A>> xs = _args.d_a1;
                             return colist<T1>::ctor::Cocons_(
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
