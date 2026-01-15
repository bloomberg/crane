#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
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
      std::shared_ptr<nat> _a0;
    };
    using variant_t = std::variant<O, S>;

  private:
    variant_t v_;
    explicit nat(O x) : v_(std::move(x)) {}
    explicit nat(S x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<nat> O_() {
        return std::shared_ptr<nat>(new nat(O{}));
      }
      static std::shared_ptr<nat> S_(const std::shared_ptr<nat> &a0) {
        return std::shared_ptr<nat>(new nat(S{a0}));
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
    std::shared_ptr<list<A>> app(const std::shared_ptr<list<A>> &m) const {
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

struct NestedTree {
  template <typename A> struct tree {
  public:
    struct leaf {};
    struct node {
      A _a0;
      std::shared_ptr<tree<std::pair<A, A>>> _a1;
    };
    using variant_t = std::variant<leaf, node>;

  private:
    variant_t v_;
    explicit tree(leaf x) : v_(std::move(x)) {}
    explicit tree(node x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<tree<A>> leaf_() {
        return std::shared_ptr<tree<A>>(new tree<A>(leaf{}));
      }
      static std::shared_ptr<tree<A>>
      node_(A a0, const std::shared_ptr<tree<std::pair<A, A>>> &a1) {
        return std::shared_ptr<tree<A>>(new tree<A>(node{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2,
            MapsTo<T1, unknown,
                   std::shared_ptr<tree<std::pair<unknown, unknown>>>, T1>
                F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree<T2>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T2>::leaf _args) -> T1 {
                     return f("dummy");
                   },
                   [&](const typename tree<T2>::node _args) -> T1 {
                     T2 y = _args._a0;
                     std::shared_ptr<tree<std::pair<T2, T2>>> t0 = _args._a1;
                     return f0("dummy", y, t0, tree_rect<T1, T2>(f, f0, t0));
                   }},
        t->v());
  }

  template <typename T1, typename T2,
            MapsTo<T1, unknown,
                   std::shared_ptr<tree<std::pair<unknown, unknown>>>, T1>
                F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree<T2>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T2>::leaf _args) -> T1 {
                     return f("dummy");
                   },
                   [&](const typename tree<T2>::node _args) -> T1 {
                     T2 y = _args._a0;
                     std::shared_ptr<tree<std::pair<T2, T2>>> t0 = _args._a1;
                     return f0("dummy", y, t0, tree_rec<T1, T2>(f, f0, t0));
                   }},
        t->v());
  }

  static inline const std::shared_ptr<tree<std::shared_ptr<Nat::nat>>>
      example1 = tree<std::shared_ptr<Nat::nat>>::ctor::node_(
          Nat::nat::ctor::S_(Nat::nat::ctor::O_()),
          tree<
              std::pair<std::shared_ptr<Nat::nat>, std::shared_ptr<Nat::nat>>>::
              ctor::node_(
                  std::make_pair(
                      Nat::nat::ctor::S_(
                          Nat::nat::ctor::S_(Nat::nat::ctor::O_())),
                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                          Nat::nat::ctor::S_(Nat::nat::ctor::O_())))),
                  tree<std::pair<std::pair<std::shared_ptr<Nat::nat>,
                                           std::shared_ptr<Nat::nat>>,
                                 std::pair<std::shared_ptr<Nat::nat>,
                                           std::shared_ptr<Nat::nat>>>>::ctor::
                      node_(
                          std::make_pair(
                              std::make_pair(
                                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                          Nat::nat::ctor::O_())))),
                                  Nat::nat::ctor::S_(
                                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                          Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                              Nat::nat::ctor::O_())))))),
                              std::make_pair(
                                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                          Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                              Nat::nat::ctor::O_())))))),
                                  Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                      Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                          Nat::nat::ctor::S_(Nat::nat::ctor::S_(
                                              Nat::nat::ctor::S_(
                                                  Nat::nat::ctor::O_()))))))))),
                          tree<std::pair<
                              std::pair<std::pair<std::shared_ptr<Nat::nat>,
                                                  std::shared_ptr<Nat::nat>>,
                                        std::pair<std::shared_ptr<Nat::nat>,
                                                  std::shared_ptr<Nat::nat>>>,
                              std::pair<
                                  std::pair<std::shared_ptr<Nat::nat>,
                                            std::shared_ptr<Nat::nat>>,
                                  std::pair<std::shared_ptr<Nat::nat>,
                                            std::shared_ptr<Nat::nat>>>>>::
                              ctor::leaf_())));

  template <typename T1, typename T2,
            MapsTo<std::shared_ptr<List::list<T2>>, T1> F0>
  static std::shared_ptr<List::list<T2>> lift(F0 &&f,
                                              const std::pair<T1, T1> p) {
    T1 x = p.first;
    T1 y = p.second;
    return f(x)->app(f(y));
  }

  template <typename T1>
  static std::shared_ptr<List::list<std::shared_ptr<List::list<T1>>>>
  flatten_tree(const std::shared_ptr<tree<T1>> &t) {
    std::function<
        std::shared_ptr<List::list<std::shared_ptr<List::list<meta25>>>>(
            std::function<std::shared_ptr<List::list<meta25>>(meta24)>,
            std::shared_ptr<tree<meta24>>)>
        go;
    go = [&](std::function<std::shared_ptr<List::list<meta25>>(meta24)> f,
             std::shared_ptr<tree<meta24>> t0)
        -> std::shared_ptr<List::list<std::shared_ptr<List::list<meta25>>>> {
      return std::visit(
          Overloaded{[&](const typename tree<meta24>::leaf _args)
                         -> std::shared_ptr<
                             List::list<std::shared_ptr<List::list<meta25>>>> {
                       return List::list<
                           std::shared_ptr<List::list<meta25>>>::ctor::nil_();
                     },
                     [&](const typename tree<meta24>::node _args)
                         -> std::shared_ptr<
                             List::list<std::shared_ptr<List::list<meta25>>>> {
                       meta24 a = _args._a0;
                       std::shared_ptr<tree<std::pair<meta24, meta24>>> t1 =
                           _args._a1;
                       return List::list<std::shared_ptr<List::list<meta25>>>::
                           ctor::cons_(f(a),
                                       go(
                                           [&](const std::pair<T4, T4> _x0) {
                                             return lift<T4, T5>(f, _x0);
                                           },
                                           t1));
                     }},
          t0->v());
    };
    return go(
        [&](T1 x) {
          return List::list<T1>::ctor::cons_(x, List::list<T1>::ctor::nil_());
        },
        t);
  }
};
