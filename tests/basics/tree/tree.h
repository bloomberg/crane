#ifndef INCLUDED_TREE
#define INCLUDED_TREE

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat max(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      auto &[a0] = std::get<typename Nat::S>(this->v());
      if (std::holds_alternative<typename Nat::O>(m.v_mut())) {
        return *this;
      } else {
        auto &[a00] = std::get<typename Nat::S>(m.v_mut());
        return Nat::s(a0->max(*a00));
      }
    }
  }

  Nat add(Nat m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(a0->add(std::move(m)));
    }
  }
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

template <typename A> struct Tree {
  /// A polymorphic binary tree. A tree is either a leaf or a
  /// node with a left subtree, a value, and a right subtree.
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree<A>> t1;
    A x;
    std::shared_ptr<Tree<A>> t2;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Leaf _v) : v_(_v) {}

  explicit Tree(Node _v) : v_(std::move(_v)) {}

  template <typename _U> explicit Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[t1, x, t2] = std::get<typename Tree<_U>::Node>(_other.v());
      this->v_ = Node{
          t1 ? std::make_shared<Tree<A>>(*t1) : nullptr,
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (x.type() == typeid(A))
                return std::any_cast<A>(x);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(x);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(x);
            } else
              return A(x);
          }(),
          t2 ? std::make_shared<Tree<A>>(*t2) : nullptr};
    }
  }

  static Tree<A> leaf() { return Tree(Leaf{}); }

  static Tree<A> node(Tree<A> t1, A x, Tree<A> t2) {
    return Tree(Node{std::make_shared<Tree<A>>(std::move(t1)), std::move(x),
                     std::make_shared<Tree<A>>(std::move(t2))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Tree<A> &, T1 &, A &, Tree<A> &,
                                   T1 &>
  T1 tree_rect(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return f0(*a0, a0->template tree_rect<T1>(f, f0), a1, *a2,
                a2->template tree_rect<T1>(f, f0));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Tree<A> &, T1 &, A &, Tree<A> &,
                                   T1 &>
  T1 tree_rec(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return f0(*a0, a0->template tree_rec<T1>(f, f0), a1, *a2,
                a2->template tree_rec<T1>(f, f0));
    }
  }

  /// Returns true if t is a leaf, false otherwise.
  Bool0 is_leaf() const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return Bool0::TRUE_;
    } else {
      return Bool0::FALSE_;
    }
  }

  /// Number of nodes in tree t. A leaf counts as 1.
  Nat size() const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return Nat::s(Nat::o()).add(a0->size()).add(a2->size());
    }
  }

  /// Height of tree t. A leaf has height 1.
  Nat height() const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return Nat::s(Nat::o()).add(a0->height().max(a2->height()));
    }
  }

  /// Collect all values in t into a list via in-order traversal.
  List<A> flatten() const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1, a2] = std::get<typename Tree<A>::Node>(this->v());
      return a0->flatten().app(List<A>::cons(a1, a2->flatten()));
    }
  }

  /// Merge two trees t1 and t2 element-wise using combine.
  /// Subtrees beyond the shape of the other tree are truncated.
  template <typename F0>
    requires std::is_invocable_r_v<A, F0 &, A &, A &>
  Tree<A> merge(F0 &&combine, const Tree<A> &t2) const {
    if (std::holds_alternative<typename Tree<A>::Leaf>(this->v())) {
      if (std::holds_alternative<typename Tree<A>::Leaf>(t2.v())) {
        return Tree<A>::leaf();
      } else {
        const auto &[a00, a10, a20] = std::get<typename Tree<A>::Node>(t2.v());
        return Tree<A>::node(Tree<A>::leaf(), a10, Tree<A>::leaf());
      }
    } else {
      const auto &[a0, a2, a3] = std::get<typename Tree<A>::Node>(this->v());
      if (std::holds_alternative<typename Tree<A>::Leaf>(t2.v())) {
        return Tree<A>::node(Tree<A>::leaf(), a2, Tree<A>::leaf());
      } else {
        const auto &[a00, a10, a20] = std::get<typename Tree<A>::Node>(t2.v());
        return Tree<A>::node(a0->merge(combine, *a00), combine(a2, a10),
                             a3->merge(combine, *a20));
      }
    }
  }

  static const Tree<Nat> &tree1() {
    static const Tree<Nat> v = Tree<Nat>::node(
        Tree<Nat>::node(Tree<Nat>::leaf(), Nat::s(Nat::s(Nat::s(Nat::o()))),
                        Tree<Nat>::node(Tree<Nat>::leaf(),
                                        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(
                                            Nat::s(Nat::s(Nat::o()))))))),
                                        Tree<Nat>::leaf())),
        Nat::s(Nat::o()),
        Tree<Nat>::node(
            Tree<Nat>::leaf(), Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
            Tree<Nat>::node(Tree<Nat>::node(Tree<Nat>::leaf(),
                                            Nat::s(Nat::s(Nat::s(Nat::s(
                                                Nat::s(Nat::s(Nat::o())))))),
                                            Tree<Nat>::leaf()),
                            Nat::s(Nat::s(Nat::o())), Tree<Nat>::leaf())));
    return v;
  }
};

#endif // INCLUDED_TREE
