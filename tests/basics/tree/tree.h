#ifndef INCLUDED_TREE
#define INCLUDED_TREE

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

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat : public std::enable_shared_from_this<Nat> {
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
  explicit Nat(O _v) : d_v_(_v) {}

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

  std::shared_ptr<Nat> max(std::shared_ptr<Nat> m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(this->v());
      if (std::holds_alternative<typename Nat::O>(m->v())) {
        return std::const_pointer_cast<Nat>(this->shared_from_this());
      } else {
        const auto &[d_a00] = std::get<typename Nat::S>(m->v());
        return Nat::s(d_a0->max(d_a00));
      }
    }
  }

  std::shared_ptr<Nat> add(std::shared_ptr<Nat> m) const {
    if (std::holds_alternative<typename Nat::O>(this->v())) {
      return m;
    } else {
      const auto &[d_a0] = std::get<typename Nat::S>(this->v());
      return Nat::s(d_a0->add(m));
    }
  }
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
  explicit List(Nil _v) : d_v_(_v) {}

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
    if (std::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(m));
    }
  }
};

template <typename t_A> struct Tree {
  /// A polymorphic binary tree. A tree is either a leaf or a
  /// node with a left subtree, a value, and a right subtree.
  // TYPES
  struct Leaf {};

  struct Node {
    std::shared_ptr<Tree<t_A>> d_a0;
    t_A d_a1;
    std::shared_ptr<Tree<t_A>> d_a2;
  };

  using variant_t = std::variant<Leaf, Node>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Tree(Leaf _v) : d_v_(_v) {}

  explicit Tree(Node _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Tree<t_A>> leaf() {
    return std::make_shared<Tree<t_A>>(Leaf{});
  }

  static std::shared_ptr<Tree<t_A>> node(const std::shared_ptr<Tree<t_A>> &a0,
                                         t_A a1,
                                         const std::shared_ptr<Tree<t_A>> &a2) {
    return std::make_shared<Tree<t_A>>(Node{a0, std::move(a1), a2});
  }

  static std::shared_ptr<Tree<t_A>> node(std::shared_ptr<Tree<t_A>> &&a0,
                                         t_A a1,
                                         std::shared_ptr<Tree<t_A>> &&a2) {
    return std::make_shared<Tree<t_A>>(
        Node{std::move(a0), std::move(a1), std::move(a2)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <typename T1, MapsTo<T1, std::shared_ptr<Tree<t_A>>, T1, t_A,
                                std::shared_ptr<Tree<t_A>>, T1>
                             F1>
  T1 tree_rect(const T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(this->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(this->v());
      return f0(d_a0, d_a0->template tree_rect<T1>(f, f0), d_a1, d_a2,
                d_a2->template tree_rect<T1>(f, f0));
    }
  }

  template <typename T1, MapsTo<T1, std::shared_ptr<Tree<t_A>>, T1, t_A,
                                std::shared_ptr<Tree<t_A>>, T1>
                             F1>
  T1 tree_rec(const T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(this->v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(this->v());
      return f0(d_a0, d_a0->template tree_rec<T1>(f, f0), d_a1, d_a2,
                d_a2->template tree_rec<T1>(f, f0));
    }
  }

  /// Returns true if t is a leaf, false otherwise.
  __attribute__((pure)) Bool0 is_leaf() const {
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(this->v())) {
      return Bool0::e_TRUE0;
    } else {
      return Bool0::e_FALSE0;
    }
  }

  /// Number of nodes in tree t. A leaf counts as 1.
  std::shared_ptr<Nat> size() const {
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(this->v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(this->v());
      return Nat::s(Nat::o())->add(d_a0->size())->add(d_a2->size());
    }
  }

  /// Height of tree t. A leaf has height 1.
  std::shared_ptr<Nat> height() const {
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(this->v())) {
      return Nat::s(Nat::o());
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(this->v());
      return Nat::s(Nat::o())->add(d_a0->height()->max(d_a2->height()));
    }
  }

  /// Collect all values in t into a list via in-order traversal.
  std::shared_ptr<List<t_A>> flatten() const {
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(this->v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(this->v());
      return d_a0->flatten()->app(List<t_A>::cons(d_a1, d_a2->flatten()));
    }
  }

  /// Merge two trees t1 and t2 element-wise using combine.
  /// Subtrees beyond the shape of the other tree are truncated.
  template <MapsTo<t_A, t_A, t_A> F0>
  std::shared_ptr<Tree<t_A>> merge(F0 &&combine,
                                   const std::shared_ptr<Tree<t_A>> &t2) const {
    if (std::holds_alternative<typename Tree<t_A>::Leaf>(this->v())) {
      if (std::holds_alternative<typename Tree<t_A>::Leaf>(t2->v())) {
        return Tree<t_A>::leaf();
      } else {
        const auto &[d_a00, d_a10, d_a20] =
            std::get<typename Tree<t_A>::Node>(t2->v());
        return Tree<t_A>::node(Tree<t_A>::leaf(), d_a10, Tree<t_A>::leaf());
      }
    } else {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename Tree<t_A>::Node>(this->v());
      if (std::holds_alternative<typename Tree<t_A>::Leaf>(t2->v())) {
        return Tree<t_A>::node(Tree<t_A>::leaf(), d_a1, Tree<t_A>::leaf());
      } else {
        const auto &[d_a00, d_a10, d_a20] =
            std::get<typename Tree<t_A>::Node>(t2->v());
        return Tree<t_A>::node(d_a0->merge(combine, d_a00),
                               combine(d_a1, d_a10),
                               d_a2->merge(combine, d_a20));
      }
    }
  }

  static const std::shared_ptr<Tree<std::shared_ptr<Nat>>> &tree1() {
    static const std::shared_ptr<Tree<std::shared_ptr<Nat>>> v =
        Tree<std::shared_ptr<Nat>>::node(
            Tree<std::shared_ptr<Nat>>::node(
                Tree<std::shared_ptr<Nat>>::leaf(),
                Nat::s(Nat::s(Nat::s(Nat::o()))),
                Tree<std::shared_ptr<Nat>>::node(
                    Tree<std::shared_ptr<Nat>>::leaf(),
                    Nat::s(Nat::s(
                        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))),
                    Tree<std::shared_ptr<Nat>>::leaf())),
            Nat::s(Nat::o()),
            Tree<std::shared_ptr<Nat>>::node(
                Tree<std::shared_ptr<Nat>>::leaf(),
                Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
                Tree<std::shared_ptr<Nat>>::node(
                    Tree<std::shared_ptr<Nat>>::node(
                        Tree<std::shared_ptr<Nat>>::leaf(),
                        Nat::s(
                            Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                        Tree<std::shared_ptr<Nat>>::leaf()),
                    Nat::s(Nat::s(Nat::o())),
                    Tree<std::shared_ptr<Nat>>::leaf())));
    return v;
  }
};

#endif // INCLUDED_TREE
