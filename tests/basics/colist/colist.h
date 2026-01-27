#include <functional>
#include <iostream>
#include <memory>
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
    explicit nat(O x) : v_(std::move(x)) {}
    explicit nat(S x) : v_(std::move(x)) {}

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
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

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
    variant_t v_;
    explicit colist(conil x) : v_(std::move(x)) {}
    explicit colist(cocons x) : v_(std::move(x)) {}

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
    };
    const variant_t &v() const { return v_; }
    std::shared_ptr<List::list<A>>
    list_of_colist(const std::shared_ptr<Nat::nat> &fuel) const {
      return std::visit(
          Overloaded{[&](const typename Nat::nat::O _args)
                         -> std::shared_ptr<List::list<A>> {
                       return List::list<A>::ctor::nil_();
                     },
                     [&](const typename Nat::nat::S _args)
                         -> std::shared_ptr<List::list<A>> {
                       std::shared_ptr<Nat::nat> fuel_ = _args._a0;
                       return std::visit(
                           Overloaded{
                               [&](const typename colist<A>::conil _args)
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
      return std::visit(Overloaded{[&](const typename colist<A>::conil _args)
                                       -> std::shared_ptr<colist<T2>> {
                                     return colist<T2>::ctor::conil_();
                                   },
                                   [&](const typename colist<A>::cocons _args)
                                       -> std::shared_ptr<colist<T2>> {
                                     A x = _args._a0;
                                     std::shared_ptr<colist<A>> xs = _args._a1;
                                     return colist<T2>::ctor::cocons_(
                                         f(x), xs->comap(f));
                                   }},
                        this->v());
    }
  };

  static std::shared_ptr<colist<std::shared_ptr<Nat::nat>>>
  nats(const std::shared_ptr<Nat::nat> &n);

  static inline const std::shared_ptr<List::list<std::shared_ptr<Nat::nat>>>
      first_three = nats(Nat::nat::ctor::O_())
                        ->list_of_colist(Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                            Nat::nat::ctor::S_(Nat::nat::ctor::O_()))));
};
