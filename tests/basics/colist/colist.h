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
  struct nat {
  public:
    struct O {};
    struct S {
      std::shared_ptr<Nat::nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O _v) : v_(std::move(_v)) {}
    explicit nat(S _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Nat::nat> O_() {
        return std::shared_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::shared_ptr<Nat::nat> S_(const std::shared_ptr<Nat::nat> &a0) {
        return std::shared_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
      static std::unique_ptr<Nat::nat> O_uptr() {
        return std::unique_ptr<Nat::nat>(new Nat::nat(O{}));
      }
      static std::unique_ptr<Nat::nat>
      S_uptr(const std::shared_ptr<Nat::nat> &a0) {
        return std::unique_ptr<Nat::nat>(new Nat::nat(S{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil _v) : v_(std::move(_v)) {}
    explicit list(cons _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
      static std::unique_ptr<List::list<A>> nil_uptr() {
        return std::unique_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::unique_ptr<List::list<A>>
      cons_uptr(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::unique_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Colist {
  template <typename A> struct colist {
  public:
    struct conil {};
    struct cocons {
      A _a0;
      std::shared_ptr<colist<A>> _a1;
    };
    using variant_t = std::variant<conil, cocons>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit colist(conil _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit colist(cocons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit colist(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
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
        return std::shared_ptr<colist<A>>(
            new colist<A>(std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<colist<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    std::shared_ptr<List::list<A>>
    list_of_colist(const std::shared_ptr<Nat::nat> &fuel) const {
      return std::visit(
          Overloaded{[](const typename Nat::nat::O _args)
                         -> std::shared_ptr<List::list<A>> {
                       return List::list<A>::ctor::nil_();
                     },
                     [&](const typename Nat::nat::S _args)
                         -> std::shared_ptr<List::list<A>> {
                       std::shared_ptr<Nat::nat> fuel_ = _args._a0;
                       return std::visit(
                           Overloaded{
                               [](const typename colist<A>::conil _args)
                                   -> std::shared_ptr<List::list<A>> {
                                 return List::list<A>::ctor::nil_();
                               },
                               [&](const typename colist<A>::cocons _args)
                                   -> std::shared_ptr<List::list<A>> {
                                 A x = _args._a0;
                                 std::shared_ptr<colist<A>> xs = _args._a1;
                                 return List::list<A>::ctor::cons_(
                                     x, xs->list_of_colist(fuel_));
                               }},
                           this->v());
                     }},
          fuel->v());
    }
    template <typename T2, MapsTo<T2, A> F0>
    std::shared_ptr<colist<T2>> comap(F0 &&f) const {
      return colist<T2>::ctor::lazy_([=](void) -> std::shared_ptr<colist<T2>> {
        return std::visit(
            Overloaded{[](const typename colist<A>::conil _args)
                           -> std::shared_ptr<colist<T2>> {
                         return colist<T2>::ctor::conil_();
                       },
                       [&](const typename colist<A>::cocons _args)
                           -> std::shared_ptr<colist<T2>> {
                         A x = _args._a0;
                         std::shared_ptr<colist<A>> xs = _args._a1;
                         return colist<T2>::ctor::cocons_(f(x), xs->comap(f));
                       }},
            this->v());
      });
    }
  };

  static std::shared_ptr<colist<std::shared_ptr<Nat::nat>>>
  nats(const std::shared_ptr<Nat::nat> &n);

  static inline const std::shared_ptr<List::list<std::shared_ptr<Nat::nat>>>
      first_three = nats(Nat::nat::ctor::O_())
                        ->list_of_colist(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                            Nat::nat::ctor::S_(Nat::nat::ctor::O_()))));
};
