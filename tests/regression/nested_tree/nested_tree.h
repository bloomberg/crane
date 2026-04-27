#ifndef INCLUDED_NESTED_TREE
#define INCLUDED_NESTED_TREE

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Nat *operator->() { return this; }

  __attribute__((pure)) const Nat *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Nat(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

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
    tree() {}

    explicit tree(Leaf _v) : d_v_(_v) {}

    explicit tree(Node _v) : d_v_(std::move(_v)) {}

    tree(const tree<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree<t_A> &operator=(const tree<t_A> &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree<t_A> &operator=(tree<t_A> &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Leaf>(_sv.v())) {
        return tree<t_A>(Leaf{});
      } else {
        const auto &[d_a0, d_a1] = std::get<Node>(_sv.v());
        return tree<t_A>(Node{d_a0, d_a1});
      }
    }

    // CREATORS
    template <typename _U> explicit tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        d_v_ = Leaf{};
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename tree<_U>::Node>(_other.v());
        d_v_ =
            Node{t_A(d_a0), std::shared_ptr<tree<std::pair<t_A, t_A>>>(d_a1)};
      }
    }

    __attribute__((pure)) static tree<t_A> leaf() { return tree(Leaf{}); }

    __attribute__((pure)) static tree<t_A>
    node(t_A a0, const tree<std::pair<t_A, t_A>> &a1) {
      return tree(Node{std::move(a0), (static_cast<void>(a1), nullptr)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) tree<t_A> *operator->() { return this; }

    __attribute__((pure)) const tree<t_A> *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = tree<t_A>(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree<T2> &t) {
    if (std::holds_alternative<typename tree<T2>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree<T2>::Node>(t.v());
      return std::any_cast<T1>(f0(
          d_a0, NestedTree::tree<std::pair<T2, T2>>(d_a1),
          tree_rect<T1, T2>(f, f0, NestedTree::tree<std::pair<T2, T2>>(d_a1))));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree<T2> &t) {
    if (std::holds_alternative<typename tree<T2>::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename tree<T2>::Node>(t.v());
      return std::any_cast<T1>(f0(
          d_a0, NestedTree::tree<std::pair<T2, T2>>(d_a1),
          tree_rec<T1, T2>(f, f0, NestedTree::tree<std::pair<T2, T2>>(d_a1))));
    }
  }

  static inline const tree<Nat> example1 = tree<Nat>::node(
      Nat::s(Nat::o()),
      tree<std::pair<Nat, Nat>>::node(
          std::make_pair(Nat::s(Nat::s(Nat::o())),
                         Nat::s(Nat::s(Nat::s(Nat::o())))),
          tree<std::pair<std::pair<Nat, Nat>, std::pair<Nat, Nat>>>::node(
              std::make_pair(
                  std::make_pair(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                  std::make_pair(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                      Nat::s(Nat::s(
                          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))),
              tree<
                  std::pair<std::pair<std::pair<Nat, Nat>, std::pair<Nat, Nat>>,
                            std::pair<std::pair<Nat, Nat>,
                                      std::pair<Nat, Nat>>>>::leaf())));

  template <typename T1, typename T2, MapsTo<List<T2>, T1> F0>
  __attribute__((pure)) static List<T2> lift(F0 &&f,
                                             const std::pair<T1, T1> &p) {
    const T1 &x = p.first;
    const T1 &y = p.second;
    return f(x).app(f(y));
  }

  template <typename T1>
  __attribute__((pure)) static List<List<T1>> flatten_tree(const tree<T1> &t) {
    return _flatten_tree_go<T1, List<List<T1>>>(
        [](const T1 x) { return List<T1>::cons(x, List<T1>::nil()); }, t);
  }
};

template <typename T1, typename T2, MapsTo<List<T2>, T1> F0>
__attribute__((pure)) List<List<T2>>
_flatten_tree_go(F0 &&f, const NestedTree::template tree<T1> t0) {
  if (std::holds_alternative<typename NestedTree::template tree<T1>::Leaf>(
          t0.v())) {
    return List<List<T2>>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NestedTree::template tree<T1>::Node>(t0.v());
    return List<List<T2>>::cons(
        f(d_a0), _flatten_tree_go<T1, T2>(
                     [=](std::pair<T1, T1> _x0) mutable -> List<T2> {
                       return NestedTree::template lift<T1, T2>(f, _x0);
                     },
                     NestedTree::tree<std::pair<T1, T1>>(d_a1)));
  }
}

#endif // INCLUDED_NESTED_TREE
