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

struct Tree {
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
      std::shared_ptr<tree<A>> _a0;
      A _a1;
      std::shared_ptr<tree<A>> _a2;
      static std::shared_ptr<tree<A>> make(std::shared_ptr<tree<A>> _a0, A _a1,
                                           std::shared_ptr<tree<A>> _a2) {
        return std::make_shared<tree<A>>(node<A>{_a0, _a1, _a2});
      }
    };
  };

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<typename Tree::tree<T1>>, T2, T1,
                   std::shared_ptr<typename Tree::tree<T1>>, T2>
                F1>
  T2 tree_rect(const T2 f, F1 &&f0,
               const std::shared_ptr<typename Tree::tree<T1>> t) {
    return std::visit(
        Overloaded{[&](const typename Tree::leaf<T1> _args) -> T2 { return f; },
                   [&](const typename Tree::node<T1> _args) -> T2 {
                     std::shared_ptr<typename Tree::tree<T1>> t0 = _args._a0;
                     T1 y = _args._a1;
                     std::shared_ptr<typename Tree::tree<T1>> t1 = _args._a2;
                     return f0(t0, tree_rect<T1, T2>(f, f0, t0), y, t1,
                               tree_rect<T1, T2>(f, f0, t1));
                   }},
        *t);
  }

  template <typename T1, typename T2,
            MapsTo<T2, std::shared_ptr<typename Tree::tree<T1>>, T2, T1,
                   std::shared_ptr<typename Tree::tree<T1>>, T2>
                F1>
  T2 tree_rec(const T2 f, F1 &&f0,
              const std::shared_ptr<typename Tree::tree<T1>> t) {
    return std::visit(
        Overloaded{[&](const typename Tree::leaf<T1> _args) -> T2 { return f; },
                   [&](const typename Tree::node<T1> _args) -> T2 {
                     std::shared_ptr<typename Tree::tree<T1>> t0 = _args._a0;
                     T1 y = _args._a1;
                     std::shared_ptr<typename Tree::tree<T1>> t1 = _args._a2;
                     return f0(t0, tree_rec<T1, T2>(f, f0, t0), y, t1,
                               tree_rec<T1, T2>(f, f0, t1));
                   }},
        *t);
  }

  template <typename T1>
  std::shared_ptr<typename List::list<T1>>
  flatten(const std::shared_ptr<typename Tree::tree<T1>> t) {
    return std::visit(
        Overloaded{[&](const typename Tree::leaf<T1> _args)
                       -> std::shared_ptr<typename List::list<T1>> {
                     return List::nil<T1>::make();
                   },
                   [&](const typename Tree::node<T1> _args)
                       -> std::shared_ptr<typename List::list<T1>> {
                     std::shared_ptr<typename Tree::tree<T1>> l = _args._a0;
                     T1 x = _args._a1;
                     std::shared_ptr<typename Tree::tree<T1>> r = _args._a2;
                     return app<T1>(flatten<T1>(l),
                                    List::cons<T1>::make(x, flatten<T1>(r)));
                   }},
        *t);
  }

  static inline const std::shared_ptr<
      typename Tree::tree<std::shared_ptr<typename Nat::nat>>>
      tree1 = Tree::node<std::shared_ptr<typename Nat::nat>>::make(
          Tree::node<std::shared_ptr<typename Nat::nat>>::make(
              Tree::leaf<std::shared_ptr<typename Nat::nat>>::make(),
              Nat::S::make(Nat::S::make(Nat::S::make(Nat::O::make()))),
              Tree::node<std::shared_ptr<typename Nat::nat>>::make(
                  Tree::leaf<std::shared_ptr<typename Nat::nat>>::make(),
                  Nat::S::make(
                      Nat::S::make(Nat::S::make(Nat::S::make(Nat::S::make(
                          Nat::S::make(Nat::S::make(Nat::O::make()))))))),
                  Tree::leaf<std::shared_ptr<typename Nat::nat>>::make())),
          Nat::S::make(Nat::O::make()),
          Tree::node<std::shared_ptr<typename Nat::nat>>::make(
              Tree::leaf<std::shared_ptr<typename Nat::nat>>::make(),
              Nat::S::make(
                  Nat::S::make(Nat::S::make(Nat::S::make(Nat::O::make())))),
              Tree::node<std::shared_ptr<typename Nat::nat>>::make(
                  Tree::node<std::shared_ptr<typename Nat::nat>>::make(
                      Tree::leaf<std::shared_ptr<typename Nat::nat>>::make(),
                      Nat::S::make(Nat::S::make(Nat::S::make(Nat::S::make(
                          Nat::S::make(Nat::S::make(Nat::O::make())))))),
                      Tree::leaf<std::shared_ptr<typename Nat::nat>>::make()),
                  Nat::S::make(Nat::S::make(Nat::O::make())),
                  Tree::leaf<std::shared_ptr<typename Nat::nat>>::make())));
};
