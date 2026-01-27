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

struct Prod {
  template <typename A, typename B> struct prod {
  public:
    struct pair {
      A _a0;
      B _a1;
    };
    using variant_t = std::variant<pair>;

  private:
    variant_t v_;
    explicit prod(pair x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Prod::prod<A, B>> pair_(A a0, B a1) {
        return std::shared_ptr<Prod::prod<A, B>>(
            new Prod::prod<A, B>(pair{a0, a1}));
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
    std::shared_ptr<List::list<A>>
    app(const std::shared_ptr<List::list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a, l1->app(m));
                     }},
          this->v());
    }
  };
};

template <typename T1>
std::shared_ptr<List::list<T1>> rev(const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[&](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 return List::list<T1>::ctor::nil_();
                               },
                               [&](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 T1 x = _args._a0;
                                 std::shared_ptr<List::list<T1>> l_ = _args._a1;
                                 return rev<T1>(l_)->app(
                                     List::list<T1>::ctor::cons_(
                                         x, List::list<T1>::ctor::nil_()));
                               }},
                    l->v());
}

template <typename T1, typename T2>
std::shared_ptr<List::list<std::shared_ptr<Prod::prod<T1, T2>>>>
better_zip(const std::shared_ptr<List::list<T1>> &la,
           const std::shared_ptr<List::list<T2>> &lb) {
  std::function<
      std::shared_ptr<List::list<std::shared_ptr<Prod::prod<T1, T2>>>>(
          std::shared_ptr<List::list<T1>>, std::shared_ptr<List::list<T2>>,
          std::shared_ptr<List::list<std::shared_ptr<Prod::prod<T1, T2>>>>)>
      go;
  go = [&](std::shared_ptr<List::list<T1>> la0,
           std::shared_ptr<List::list<T2>> lb0,
           std::shared_ptr<List::list<std::shared_ptr<Prod::prod<T1, T2>>>> acc)
      -> std::shared_ptr<List::list<std::shared_ptr<Prod::prod<T1, T2>>>> {
    return std::visit(
        Overloaded{
            [&](const typename List::list<T1>::nil _args)
                -> std::shared_ptr<
                    List::list<std::shared_ptr<Prod::prod<T1, T2>>>> {
              return rev<std::shared_ptr<Prod::prod<T1, T2>>>(acc);
            },
            [&](const typename List::list<T1>::cons _args)
                -> std::shared_ptr<
                    List::list<std::shared_ptr<Prod::prod<T1, T2>>>> {
              T1 x = _args._a0;
              std::shared_ptr<List::list<T1>> xs = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List::list<T2>::nil _args)
                          -> std::shared_ptr<
                              List::list<std::shared_ptr<Prod::prod<T1, T2>>>> {
                        return rev<std::shared_ptr<Prod::prod<T1, T2>>>(acc);
                      },
                      [&](const typename List::list<T2>::cons _args)
                          -> std::shared_ptr<
                              List::list<std::shared_ptr<Prod::prod<T1, T2>>>> {
                        T2 y = _args._a0;
                        std::shared_ptr<List::list<T2>> ys = _args._a1;
                        return go(
                            xs, ys,
                            List::list<std::shared_ptr<Prod::prod<T1, T2>>>::
                                ctor::cons_(
                                    Prod::prod<T1, T2>::ctor::pair_(x, y),
                                    acc));
                      }},
                  lb0->v());
            }},
        la0->v());
  };
  return go(la, lb,
            List::list<std::shared_ptr<Prod::prod<T1, T2>>>::ctor::nil_());
}
