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
  struct O;
  struct S;
  using nat = std::variant<O, S>;
  struct O {
    static std::shared_ptr<nat> make();
  };
  struct S {
    std::shared_ptr<nat> _a0;
    static std::shared_ptr<nat> make(std::shared_ptr<nat> _a0);
  };
};

struct List {
  template <typename A> struct nil;
  template <typename A> struct cons;
  template <typename A> using list = std::variant<nil<A>, cons<A>>;
  template <typename A> struct nil {
    static std::shared_ptr<list<A>> make() {
      return std::make_shared<list<A>>(nil<A>{});
    }
  };
  template <typename A> struct cons {
    A _a0;
    std::shared_ptr<list<A>> _a1;
    static std::shared_ptr<list<A>> make(A _a0, std::shared_ptr<list<A>> _a1) {
      return std::make_shared<list<A>>(cons<A>{_a0, _a1});
    }
  };
};

template <typename T1>
std::shared_ptr<typename List::list<T1>>
app(const std::shared_ptr<typename List::list<T1>> l,
    const std::shared_ptr<typename List::list<T1>> m) {
  return std::visit(
      Overloaded{[&](const typename List::nil<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> { return m; },
                 [&](const typename List::cons<T1> _args)
                     -> std::shared_ptr<typename List::list<T1>> {
                   T1 a = _args._a0;
                   std::shared_ptr<typename List::list<T1>> l1 = _args._a1;
                   return List::cons<T1>::make(a, app<T1>(l1, m));
                 }},
      *l);
}

struct NestedTree {
  struct Tree {
    template <typename A> struct leaf;
    template <typename A> struct node;
    template <typename A> using tree = std::variant<leaf<A>, node<A>>;
    template <typename A> struct leaf {
      static std::shared_ptr<tree<A>> make() {
        return std::make_shared<tree<A>>(leaf<A>{});
      }
    };
    template <typename A> struct node {
      A _a0;
      std::shared_ptr<tree<std::pair<A, A>>> _a1;
      static std::shared_ptr<tree<A>>
      make(A _a0, std::shared_ptr<tree<std::pair<A, A>>> _a1) {
        return std::make_shared<tree<A>>(node<A>{_a0, _a1});
      }
    };
  };

  template <
      typename T1, typename T2,
      MapsTo<T1, unknown,
             std::shared_ptr<typename Tree::tree<std::pair<unknown, unknown>>>,
             T1>
          F1>
  T1 tree_rect(const T1 f, F1 &&f0,
               const std::shared_ptr<typename Tree::tree<T2>> t) {
    return std::visit(
        Overloaded{
            [&](const typename Tree::leaf<T2> _args) -> T1 {
              return f("dummy");
            },
            [&](const typename Tree::node<T2> _args) -> T1 {
              T2 y = _args._a0;
              std::shared_ptr<typename Tree::tree<std::pair<T2, T2>>> t0 =
                  _args._a1;
              return f0("dummy", y, t0, tree_rect<T1, T2>(f, f0, t0));
            }},
        *t);
  }

  template <
      typename T1, typename T2,
      MapsTo<T1, unknown,
             std::shared_ptr<typename Tree::tree<std::pair<unknown, unknown>>>,
             T1>
          F1>
  T1 tree_rec(const T1 f, F1 &&f0,
              const std::shared_ptr<typename Tree::tree<T2>> t) {
    return std::visit(
        Overloaded{
            [&](const typename Tree::leaf<T2> _args) -> T1 {
              return f("dummy");
            },
            [&](const typename Tree::node<T2> _args) -> T1 {
              T2 y = _args._a0;
              std::shared_ptr<typename Tree::tree<std::pair<T2, T2>>> t0 =
                  _args._a1;
              return f0("dummy", y, t0, tree_rec<T1, T2>(f, f0, t0));
            }},
        *t);
  }

  static inline const std::shared_ptr<
      typename Tree::tree<std::shared_ptr<typename Nat::nat>>>
      example1 = Tree::node<std::shared_ptr<typename Nat::nat>>::make(
          Nat::S::make(Nat::O::make()),
          Tree::node<std::pair<std::shared_ptr<typename Nat::nat>,
                               std::shared_ptr<typename Nat::nat>>>::
              make(
                  std::make_pair(
                      Nat::S::make(Nat::S::make(Nat::O::make())),
                      Nat::S::make(Nat::S::make(Nat::S::make(Nat::O::make())))),
                  Tree::node<std::pair<
                      std::pair<std::shared_ptr<typename Nat::nat>,
                                std::shared_ptr<typename Nat::nat>>,
                      std::pair<std::shared_ptr<typename Nat::nat>,
                                std::shared_ptr<typename Nat::nat>>>>::
                      make(
                          std::make_pair(
                              std::make_pair(
                                  Nat::S::make(Nat::S::make(Nat::S::make(
                                      Nat::S::make(Nat::O::make())))),
                                  Nat::S::make(
                                      Nat::S::make(Nat::S::make(Nat::S::make(
                                          Nat::S::make(Nat::O::make())))))),
                              std::make_pair(
                                  Nat::S::make(Nat::S::make(
                                      Nat::S::make(Nat::S::make(Nat::S::make(
                                          Nat::S::make(Nat::O::make())))))),
                                  Nat::S::make(Nat::S::make(Nat::S::make(
                                      Nat::S::make(Nat::S::make(Nat::S::make(
                                          Nat::S::make(Nat::O::make()))))))))),
                          Tree::leaf<std::pair<
                              std::pair<
                                  std::pair<std::shared_ptr<typename Nat::nat>,
                                            std::shared_ptr<typename Nat::nat>>,
                                  std::pair<
                                      std::shared_ptr<typename Nat::nat>,
                                      std::shared_ptr<typename Nat::nat>>>,
                              std::pair<
                                  std::pair<std::shared_ptr<typename Nat::nat>,
                                            std::shared_ptr<typename Nat::nat>>,
                                  std::pair<
                                      std::shared_ptr<typename Nat::nat>,
                                      std::shared_ptr<typename Nat::nat>>>>>::
                              make())));

  template <typename T1, typename T2,
            MapsTo<std::shared_ptr<typename List::list<T2>>, T1> F0>
  std::shared_ptr<typename List::list<T2>> lift(F0 &&f,
                                                const std::pair<T1, T1> p) {
    T1 x = p.first;
    T1 y = p.second;
    return app<T2>(f(x), f(y));
  }

  template <typename T1>
  std::shared_ptr<typename List::list<std::shared_ptr<typename List::list<T1>>>>
  flatten_tree(const std::shared_ptr<typename Tree::tree<T1>> t) {
    std::function<std::shared_ptr<
        typename List::list<std::shared_ptr<typename List::list<meta25>>>>(
        std::function<std::shared_ptr<typename List::list<meta25>>(meta24)>,
        std::shared_ptr<typename Tree::tree<meta24>>)>
        go;
    go = [&](std::function<std::shared_ptr<typename List::list<meta25>>(meta24)>
                 f,
             std::shared_ptr<typename Tree::tree<meta24>> t0)
        -> std::shared_ptr<
            typename List::list<std::shared_ptr<typename List::list<meta25>>>> {
      return std::visit(
          Overloaded{
              [&](const typename Tree::leaf<meta24> _args)
                  -> std::shared_ptr<typename List::list<
                      std::shared_ptr<typename List::list<meta25>>>> {
                return List::nil<
                    std::shared_ptr<typename List::list<meta25>>>::make();
              },
              [&](const typename Tree::node<meta24> _args)
                  -> std::shared_ptr<typename List::list<
                      std::shared_ptr<typename List::list<meta25>>>> {
                meta24 a = _args._a0;
                std::shared_ptr<typename Tree::tree<std::pair<meta24, meta24>>>
                    t1 = _args._a1;
                return List::
                    cons<std::shared_ptr<typename List::list<meta25>>>::make(
                        f(a), go(
                                  [&](const std::pair<T4, T4> _x0) {
                                    return lift<T4, T5>(f, _x0);
                                  },
                                  t1));
              }},
          *t0);
    };
    return go(
        [&](T1 x) { return List::cons<T1>::make(x, List::nil<T1>::make()); },
        t);
  }
};
