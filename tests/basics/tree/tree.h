#ifndef INCLUDED_TREE
#define INCLUDED_TREE

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Nat clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<O>(_sv.v())) {
      return Nat(O{});
    } else {
      const auto &[d_a0] = std::get<S>(_sv.v());
      return Nat(S{d_a0 ? std::make_unique<Nat>(d_a0->clone()) : nullptr});
    }
  }

  // CREATORS
  __attribute__((pure)) static Nat o() { return Nat(O{}); }

  __attribute__((pure)) static Nat s(const Nat &a0) {
    return Nat(S{std::make_unique<Nat>(a0)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) Nat max(Nat m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(_sv.v());
      if (std::holds_alternative<typename Nat::O>(m.v())) {
        return *(this);
      } else {
        const auto &[d_a00] = std::get<typename Nat::S>(m.v());
        return Nat::s((*(d_a0)).max(*(d_a00)));
      }
    }
  }

  __attribute__((pure)) Nat add(Nat m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Nat::O>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(_sv.v());
      return Nat::s((*(d_a0)).add(m));
    }
  }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};

template <typename t_A> struct Tree {
  /// A polymorphic binary tree. A tree is either a leaf or a
  /// node with a left subtree, a value, and a right subtree.
  // TYPES
  struct Leaf {};

  struct Node {
    std::unique_ptr<Tree<t_A>> d_a0;
    t_A d_a1;
    std::unique_ptr<Tree<t_A>> d_a2;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Tree() {}

  explicit Tree(Leaf _v) : d_v_(_v) {}

  explicit Tree(Node _v) : d_v_(std::move(_v)) {}

  Tree(const Tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Tree(Tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  Tree<t_A> &operator=(const Tree<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Tree<t_A> &operator=(Tree<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Tree<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Leaf>(_sv.v())) {
      return Tree<t_A>(Leaf{});
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<Node>(_sv.v());
      return Tree<t_A>(Node{
          d_a0 ? std::make_unique<Tree<t_A>>(d_a0->clone()) : nullptr, d_a1,
          d_a2 ? std::make_unique<Tree<t_A>>(d_a2->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      d_v_ = Leaf{};
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<_U>::Node>(_other.v());
      d_v_ =
          Node{d_a0 ? std::make_unique<Tree<t_A>>(*d_a0) : nullptr, t_A(d_a1),
               d_a2 ? std::make_unique<Tree<t_A>>(*d_a2) : nullptr};
    }
  }

  __attribute__((pure)) static Tree<t_A> leaf() { return Tree(Leaf{}); }

  __attribute__((pure)) static Tree<t_A> node(const Tree<t_A> &a0, t_A a1,
                                              const Tree<t_A> &a2) {
    return Tree(Node{std::make_unique<Tree<t_A>>(a0), std::move(a1),
                     std::make_unique<Tree<t_A>>(a2)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, Tree<t_A>, T1, t_A, Tree<t_A>, T1> F1>
  T1 tree_rect(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(_sv.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(_sv.v());
      return f0(*(d_a0), (*(d_a0)).template tree_rect<T1>(f, f0), d_a1, *(d_a2),
                (*(d_a2)).template tree_rect<T1>(f, f0));
    }
  }

  template <typename T1, MapsTo<T1, Tree<t_A>, T1, t_A, Tree<t_A>, T1> F1>
  T1 tree_rec(const T1 f, F1 &&f0) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(_sv.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(_sv.v());
      return f0(*(d_a0), (*(d_a0)).template tree_rec<T1>(f, f0), d_a1, *(d_a2),
                (*(d_a2)).template tree_rec<T1>(f, f0));
    }
  }

  /// Returns true if t is a leaf, false otherwise.
  __attribute__((pure)) Bool0 is_leaf() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(_sv.v())) {
      return Bool0::e_TRUE0;
    } else {
      return Bool0::e_FALSE0;
    }
  }

  /// Number of nodes in tree t. A leaf counts as 1.
  __attribute__((pure)) Nat size() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(_sv.v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(_sv.v());
      return Nat::s(Nat::o()).add((*(d_a0)).size()).add((*(d_a2)).size());
    }
  }

  /// Height of tree t. A leaf has height 1.
  __attribute__((pure)) Nat height() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(_sv.v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(_sv.v());
      return Nat::s(Nat::o()).add((*(d_a0)).height().max((*(d_a2)).height()));
    }
  }

  /// Collect all values in t into a list via in-order traversal.
  __attribute__((pure)) List<t_A> flatten() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(_sv.v());
      return (*(d_a0)).flatten().app(
          List<t_A>::cons(d_a1, (*(d_a2)).flatten()));
    }
  }

  /// Merge two trees t1 and t2 element-wise using combine.
  /// Subtrees beyond the shape of the other tree are truncated.
  template <MapsTo<t_A, t_A, t_A> F0>
  __attribute__((pure)) Tree<t_A> merge(F0 &&combine,
                                        const Tree<t_A> &t2) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(_sv.v())) {
      if (std::holds_alternative<typename Tree<t_A>::Leaf>(t2.v())) {
        return Tree<t_A>::leaf();
      } else {
        const auto &[d_a00, d_a10, d_a20] =
            std::get<typename Tree<t_A>::Node>(t2.v());
        return Tree<t_A>::node(Tree<t_A>::leaf(), d_a10, Tree<t_A>::leaf());
      }
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(_sv.v());
      if (std::holds_alternative<typename Tree<t_A>::Leaf>(t2.v())) {
        return Tree<t_A>::node(Tree<t_A>::leaf(), d_a1, Tree<t_A>::leaf());
      } else {
        const auto &[d_a00, d_a10, d_a20] =
            std::get<typename Tree<t_A>::Node>(t2.v());
        return Tree<t_A>::node((*(d_a0)).merge(combine, *(d_a00)),
                               combine(d_a1, d_a10),
                               (*(d_a2)).merge(combine, *(d_a20)));
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
