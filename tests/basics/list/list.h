#include <algorithm>
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

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
    template <typename T2, MapsTo<T2, A> F0>
    std::shared_ptr<list<T2>> map(F0 &&f) const {
      return std::visit(Overloaded{[&](const typename list<A>::nil _args)
                                       -> std::shared_ptr<list<T2>> {
                                     return list<T2>::ctor::nil_();
                                   },
                                   [&](const typename list<A>::cons _args)
                                       -> std::shared_ptr<list<T2>> {
                                     A x = _args._a0;
                                     std::shared_ptr<list<A>> l_ = _args._a1;
                                     return list<T2>::ctor::cons_(f(x),
                                                                  l_->map(f));
                                   }},
                        this->v());
    }
    std::shared_ptr<list<A>> app(const std::shared_ptr<list<A>> &l2) const {
      return std::visit(
          Overloaded{[&](const typename list<A>::nil _args)
                         -> std::shared_ptr<list<A>> { return l2; },
                     [&](const typename list<A>::cons _args)
                         -> std::shared_ptr<list<A>> {
                       A x = _args._a0;
                       std::shared_ptr<list<A>> l3 = _args._a1;
                       return list<A>::ctor::cons_(x, l3->app(l2));
                     }},
          this->v());
    }
    A last(const A x) const {
      return std::visit(
          Overloaded{[&](const typename list<A>::nil _args) -> A { return x; },
                     [&](const typename list<A>::cons _args) -> A {
                       A y = _args._a0;
                       std::shared_ptr<list<A>> ls = _args._a1;
                       return ls->last(y);
                     }},
          this->v());
    }
    A hd(const A x) const {
      return std::visit(
          Overloaded{[&](const typename list<A>::nil _args) -> A { return x; },
                     [&](const typename list<A>::cons _args) -> A {
                       A y = _args._a0;
                       return y;
                     }},
          this->v());
    }
    std::shared_ptr<list<A>> tl() const {
      return std::visit(Overloaded{[&](const typename list<A>::nil _args)
                                       -> std::shared_ptr<list<A>> {
                                     return list<A>::ctor::nil_();
                                   },
                                   [&](const typename list<A>::cons _args)
                                       -> std::shared_ptr<list<A>> {
                                     std::shared_ptr<list<A>> ls = _args._a1;
                                     return ls;
                                   }},
                        this->v());
    }
    template <typename T2, MapsTo<T2, A, std::shared_ptr<list<A>>, T2> F1>
    T2 list_rec(const T2 f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename list<A>::nil _args) -> T2 { return f; },
                     [&](const typename list<A>::cons _args) -> T2 {
                       A y = _args._a0;
                       std::shared_ptr<list<A>> l0 = _args._a1;
                       return f0(y, l0, l0->list_rec(f, f0));
                     }},
          this->v());
    }
    template <typename T2, MapsTo<T2, A, std::shared_ptr<list<A>>, T2> F1>
    T2 list_rect(const T2 f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename list<A>::nil _args) -> T2 { return f; },
                     [&](const typename list<A>::cons _args) -> T2 {
                       A y = _args._a0;
                       std::shared_ptr<list<A>> l0 = _args._a1;
                       return f0(y, l0, l0->list_rect(f, f0));
                     }},
          this->v());
    }
  };

  static inline const std::shared_ptr<list<unsigned int>> mytest =
      list<unsigned int>::ctor::cons_(
          3u, list<unsigned int>::ctor::cons_(
                  1u, list<unsigned int>::ctor::cons_(
                          2u, list<unsigned int>::ctor::nil_())))
          ->app(list<unsigned int>::ctor::cons_(
              8u, list<unsigned int>::ctor::cons_(
                      3u, list<unsigned int>::ctor::cons_(
                              7u, list<unsigned int>::ctor::cons_(
                                      9u, list<unsigned int>::ctor::nil_())))));
};
