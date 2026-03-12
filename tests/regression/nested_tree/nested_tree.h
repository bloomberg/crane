#ifndef INCLUDED_NESTED_TREE
#define INCLUDED_NESTED_TREE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
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
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> _a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Nat(O _v) : v_(std::move(_v)) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

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
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  std::shared_ptr<List<A>> app(std::shared_ptr<List<A>> m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
                                 }},
                      this->v());
  }
};

struct NestedTree {
  template <typename A> struct tree {
    // TYPES
    struct leaf {};

    struct node {
      A _a0;
      std::shared_ptr<tree<std::pair<A, A>>> _a1;
    };

    using variant_t = std::variant<leaf, node>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit tree(leaf _v) : v_(std::move(_v)) {}

    explicit tree(node _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<tree<A>> leaf_() {
        return std::shared_ptr<tree<A>>(new tree<A>(leaf{}));
      }

      static std::shared_ptr<tree<A>>
      node_(A a0, const std::shared_ptr<tree<std::pair<A, A>>> &a1) {
        return std::shared_ptr<tree<A>>(new tree<A>(node{a0, a1}));
      }

      static std::unique_ptr<tree<A>> leaf_uptr() {
        return std::unique_ptr<tree<A>>(new tree<A>(leaf{}));
      }

      static std::unique_ptr<tree<A>>
      node_uptr(A a0, const std::shared_ptr<tree<std::pair<A, A>>> &a1) {
        return std::unique_ptr<tree<A>>(new tree<A>(node{a0, a1}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const std::shared_ptr<tree<T2>> &t) {
    return std::visit(
        Overloaded{
            [&](const typename tree<T2>::leaf _args) -> T1 { return f(); },
            [&](const typename tree<T2>::node _args) -> T1 {
              T2 y = _args._a0;
              std::shared_ptr<tree<std::pair<T2, T2>>> t0 = _args._a1;
              return f0(y, t0, tree_rect<T1, T2>(f, f0, t0));
            }},
        t->v());
  }

  template <typename T1, typename T2, typename F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const std::shared_ptr<tree<T2>> &t) {
    return std::visit(
        Overloaded{
            [&](const typename tree<T2>::leaf _args) -> T1 { return f(); },
            [&](const typename tree<T2>::node _args) -> T1 {
              T2 y = _args._a0;
              std::shared_ptr<tree<std::pair<T2, T2>>> t0 = _args._a1;
              return f0(y, t0, tree_rec<T1, T2>(f, f0, t0));
            }},
        t->v());
  }

  static inline const std::shared_ptr<tree<std::shared_ptr<Nat>>> example1 =
      tree<std::shared_ptr<Nat>>::ctor::node_(
          Nat::ctor::S_(Nat::ctor::O_()),
          tree<std::pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>::ctor::
              node_(
                  std::make_pair(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_())),
                                 Nat::ctor::S_(Nat::ctor::S_(
                                     Nat::ctor::S_(Nat::ctor::O_())))),
                  tree<std::pair<
                      std::pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>,
                      std::pair<std::shared_ptr<Nat>, std::shared_ptr<Nat>>>>::
                      ctor::node_(
                          std::make_pair(
                              std::make_pair(
                                  Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                                      Nat::ctor::S_(Nat::ctor::O_())))),
                                  Nat::ctor::S_(
                                      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                                          Nat::ctor::S_(Nat::ctor::O_())))))),
                              std::make_pair(
                                  Nat::ctor::S_(Nat::ctor::S_(
                                      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                                          Nat::ctor::S_(Nat::ctor::O_())))))),
                                  Nat::ctor::S_(Nat::ctor::S_(
                                      Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(
                                          Nat::ctor::S_(Nat::ctor::S_(
                                              Nat::ctor::O_()))))))))),
                          tree<std::pair<
                              std::pair<std::pair<std::shared_ptr<Nat>,
                                                  std::shared_ptr<Nat>>,
                                        std::pair<std::shared_ptr<Nat>,
                                                  std::shared_ptr<Nat>>>,
                              std::pair<std::pair<std::shared_ptr<Nat>,
                                                  std::shared_ptr<Nat>>,
                                        std::pair<std::shared_ptr<Nat>,
                                                  std::shared_ptr<Nat>>>>>::
                              ctor::leaf_())));

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
        [](T1 x) { return List<T1>::ctor::cons_(x, List<T1>::ctor::nil_()); },
        t);
  }
};

template <typename T1, typename T2, MapsTo<std::shared_ptr<List<T2>>, T1> F0>
std::shared_ptr<List<std::shared_ptr<List<T2>>>>
_flatten_tree_go(F0 &&f,
                 const std::shared_ptr<NestedTree::template tree<T1>> &t0) {
  return std::visit(
      Overloaded{
          [](const typename NestedTree::template tree<T1>::leaf _args)
              -> std::shared_ptr<List<std::shared_ptr<List<T2>>>> {
            return List<std::shared_ptr<List<T2>>>::ctor::nil_();
          },
          [&](const typename NestedTree::template tree<T1>::node _args)
              -> std::shared_ptr<List<std::shared_ptr<List<T2>>>> {
            T1 a = _args._a0;
            std::shared_ptr<NestedTree::template tree<std::pair<T1, T1>>> t1 =
                _args._a1;
            return List<std::shared_ptr<List<T2>>>::ctor::cons_(
                f(a),
                _flatten_tree_go<T1, T2>(
                    [&](std::pair<T1, T1> _x0) -> std::shared_ptr<List<T2>> {
                      return NestedTree::template lift<T1, T2>(f, _x0);
                    },
                    std::move(t1)));
          }},
      t0->v());
}

#endif // INCLUDED_NESTED_TREE
