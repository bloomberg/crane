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
    };
    const variant_t &v() const { return v_; }
  };
};

struct Stream {
  template <typename A> struct stream {
  public:
    struct scons {
      A _a0;
      std::shared_ptr<stream<A>> _a1;
    };
    using variant_t = std::variant<scons>;

  private:
    crane::lazy<variant_t> lazy_v_;
    explicit stream(scons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}
    explicit stream(std::function<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<stream<A>>
      scons_(A a0, const std::shared_ptr<stream<A>> &a1) {
        return std::shared_ptr<stream<A>>(new stream<A>(scons{a0, a1}));
      }
      static std::shared_ptr<stream<A>>
      lazy_(std::function<std::shared_ptr<stream<A>>()> thunk) {
        return std::shared_ptr<stream<A>>(
            new stream<A>(std::function<variant_t()>([=](void) -> variant_t {
              std::shared_ptr<stream<A>> _tmp = thunk();
              return std::move(const_cast<variant_t &>(_tmp->v()));
            })));
      }
    };
    const variant_t &v() const { return lazy_v_.force(); }
    std::shared_ptr<List::list<A>>
    take(const std::shared_ptr<Nat::nat> &n) const {
      return std::visit(
          Overloaded{[](const typename Nat::nat::O _args)
                         -> std::shared_ptr<List::list<A>> {
                       return List::list<A>::ctor::nil_();
                     },
                     [&](const typename Nat::nat::S _args)
                         -> std::shared_ptr<List::list<A>> {
                       std::shared_ptr<Nat::nat> n_ = _args._a0;
                       return std::visit(
                           Overloaded{[&](const typename stream<A>::scons _args)
                                          -> std::shared_ptr<List::list<A>> {
                             A x = _args._a0;
                             std::shared_ptr<stream<A>> xs = _args._a1;
                             return List::list<A>::ctor::cons_(x, xs->take(n_));
                           }},
                           this->v());
                     }},
          n->v());
    }
    std::shared_ptr<stream<A>>
    interleave(const std::shared_ptr<stream<A>> &sb) const {
      return stream<A>::ctor::lazy_([=](void) -> std::shared_ptr<stream<A>> {
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
    return stream<T1>::ctor::lazy_([=](void) -> std::shared_ptr<stream<T1>> {
      return stream<T1>::ctor::scons_(x, repeat<T1>(x));
    });
  }

  static std::shared_ptr<stream<std::shared_ptr<Nat::nat>>>
  nats_from(const std::shared_ptr<Nat::nat> &n);

  static inline const std::shared_ptr<stream<std::shared_ptr<Nat::nat>>> ones =
      repeat<std::shared_ptr<Nat::nat>>(
          Nat::nat::ctor::S_(Nat::nat::ctor::O_()));

  static inline const std::shared_ptr<List::list<std::shared_ptr<Nat::nat>>>
      first_five_nats =
          nats_from(Nat::nat::ctor::O_())
              ->take(Nat::nat::ctor::S_(
                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                      Nat::nat::ctor::S_(Nat::nat::ctor::O_()))))));

  static inline const std::shared_ptr<List::list<std::shared_ptr<Nat::nat>>>
      first_five_ones =
          ones->take(Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
              Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::O_()))))));

  static inline const std::shared_ptr<List::list<std::shared_ptr<Nat::nat>>>
      interleaved =
          nats_from(Nat::nat::ctor::O_())
              ->interleave(repeat<std::shared_ptr<Nat::nat>>(
                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                          Nat::nat::ctor::S_(Nat::nat::ctor::O_())))))))))
              ->take(Nat::nat::ctor::S_(
                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                          Nat::nat::ctor::S_(Nat::nat::ctor::O_())))))))));
};
