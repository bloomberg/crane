#ifndef INCLUDED_NESTED_TREE
#define INCLUDED_NESTED_TREE

#include <memory>
#include <type_traits>
#include <utility>
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

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

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

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  std::shared_ptr<List<t_A>> app(std::shared_ptr<List<t_A>> m) const {
    return std::visit(
        Overloaded{[&](const typename List<t_A>::Nil _args)
                       -> std::shared_ptr<List<t_A>> { return m; },
                   [&](const typename List<t_A>::Cons _args)
                       -> std::shared_ptr<List<t_A>> {
                     return List<t_A>::cons(_args.d_a0, _args.d_a1->app(m));
                   }},
        this->v());
  }
};

struct NestedTree {
  template <typename t_A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      t_A d_a0;
      std::shared_ptr<tree<std::pair<t_A, t_A>>> d_a1;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit tree(Leaf _v) : d_v_(std::move(_v)) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<tree<t_A>> leaf() {
      return std::make_shared<tree<t_A>>(Leaf{});
    }

    static std::shared_ptr<tree<t_A>>
    node(t_A a0, const std::shared_ptr<tree<std::pair<t_A, t_A>>> &a1) {
      return std::make_shared<tree<t_A>>(Node{std::move(a0), a1});
    }

    static std::shared_ptr<tree<t_A>>
    node(t_A a0, std::shared_ptr<tree<std::pair<t_A, t_A>>> &&a1) {
      return std::make_shared<tree<t_A>>(Node{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree<T2>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T2>::Leaf _args) -> T1 { return f; },
                   [&](const typename tree<T2>::Node _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1,
                               tree_rect<T1, T2>(f, f0, _args.d_a1));
                   }},
        t->v());
  }

  template <typename T1, typename T2, typename F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree<T2>> &t) {
    return std::visit(
        Overloaded{[&](const typename tree<T2>::Leaf _args) -> T1 { return f; },
                   [&](const typename tree<T2>::Node _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1,
                               tree_rec<T1, T2>(f, f0, _args.d_a1));
                   }},
        t->v());
  }

  static inline const std::shared_ptr<tree<std::shared_ptr<Nat>>> example1 =
      tree<std::shared_ptr<Nat>>::node(
          Nat::s(Nat::o()),
          tree<std::pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>::node(
              std::make_pair(Nat::s(Nat::s(Nat::o())),
                             Nat::s(Nat::s(Nat::s(Nat::o())))),
              tree<std::pair<
                  std::pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>,
                  std::pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>>::
                  node(
                      std::make_pair(
                          std::make_pair(
                              Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
                              Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                          std::make_pair(Nat::s(Nat::s(Nat::s(Nat::s(
                                             Nat::s(Nat::s(Nat::o())))))),
                                         Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                                             Nat::s(Nat::s(Nat::o()))))))))),
                      tree<std::pair<
                          std::pair<std::pair<std::shared_ptr<Nat>,
                                              std::shared_ptr<Nat>>,
                                    std::pair<std::shared_ptr<Nat>,
                                              std::shared_ptr<Nat>>>,
                          std::pair<std::pair<std::shared_ptr<Nat>,
                                              std::shared_ptr<Nat>>,
                                    std::pair<std::shared_ptr<Nat>,
                                              std::shared_ptr<Nat>>>>>::
                          leaf())));

  template <typename T1, typename T2, MapsTo<std::shared_ptr<List<T2>>, T1> F0>
  static std::shared_ptr<List<T2>> lift(F0 &&f, const std::pair<T1, T1> p) {
    T1 x = p.first;
    T1 y = p.second;
    return f(x)->app(f(y));
  }

  template <typename T1>
  static std::shared_ptr<List<std::shared_ptr<List<T1>>>>
  flatten_tree(const std::shared_ptr<tree<T1>> &t) {
    return _flatten_tree_go<T1,
                            std::shared_ptr<List<std::shared_ptr<List<T1>>>>>(
        [](T1 x) { return List<T1>::cons(x, List<T1>::nil()); }, t);
  }
};

template <typename T1, typename T2, MapsTo<std::shared_ptr<List<T2>>, T1> F0>
std::shared_ptr<List<std::shared_ptr<List<T2>>>>
_flatten_tree_go(F0 &&f,
                 const std::shared_ptr<NestedTree::template tree<T1>> &t0) {
  return std::visit(
      Overloaded{[](const typename NestedTree::template tree<T1>::Leaf _args)
                     -> std::shared_ptr<List<std::shared_ptr<List<T2>>>> {
                   return List<std::shared_ptr<List<T2>>>::nil();
                 },
                 [&](const typename NestedTree::template tree<T1>::Node _args)
                     -> std::shared_ptr<List<std::shared_ptr<List<T2>>>> {
                   return List<std::shared_ptr<List<T2>>>::cons(
                       f(_args.d_a0),
                       _flatten_tree_go<T1, T2>(
                           [=](std::pair<T1, T1> _x0) mutable
                               -> std::shared_ptr<List<T2>> {
                             return NestedTree::template lift<T1, T2>(f, _x0);
                           },
                           _args.d_a1));
                 }},
      t0->v());
}

#endif // INCLUDED_NESTED_TREE
