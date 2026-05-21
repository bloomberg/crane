#ifndef INCLUDED_TREE
#define INCLUDED_TREE

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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

  Nat(const Nat &_other) : v_(std::move(_other.clone().v_)) {}

  Nat(Nat &&_other) noexcept : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->v_ = S{_alt.a0 ? std::make_shared<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::shared_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ = Cons{_alt.a, _alt.l ? std::make_shared<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.l) {
          _stack.push_back({_alt.l.get(), _dst_alt.l.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a), l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.l) {
          _stack.push_back(std::move(_alt.l));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

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

  Tree(const Tree<A> &_other) : v_(std::move(_other.clone().v_)) {}

  Tree(Tree<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  Tree<A> &operator=(const Tree<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Tree<A> &operator=(Tree<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Tree<A> clone() const {
    Tree<A> _out{};

    struct _CloneFrame {
      const Tree<A> *_src;
      Tree<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Tree<A> *_src = _frame._src;
      Tree<A> *_dst = _frame._dst;
      if (std::holds_alternative<Leaf>(_src->v())) {
        _dst->v_ = Leaf{};
      } else {
        const auto &_alt = std::get<Node>(_src->v());
        _dst->v_ = Node{_alt.t1 ? std::make_shared<Tree<A>>() : nullptr, _alt.x,
                        _alt.t2 ? std::make_shared<Tree<A>>() : nullptr};
        auto &_dst_alt = std::get<Node>(_dst->v_);
        if (_alt.t1) {
          _stack.push_back({_alt.t1.get(), _dst_alt.t1.get()});
        }
        if (_alt.t2) {
          _stack.push_back({_alt.t2.get(), _dst_alt.t2.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit Tree(const Tree<_U> &_other) {
    if (std::holds_alternative<typename Tree<_U>::Leaf>(_other.v())) {
      this->v_ = Leaf{};
    } else {
      const auto &[t1, x, t2] = std::get<typename Tree<_U>::Node>(_other.v());
      this->v_ = Node{t1 ? std::make_shared<Tree<A>>(*t1) : nullptr, A(x),
                      t2 ? std::make_shared<Tree<A>>(*t2) : nullptr};
    }
  }

  static Tree<A> leaf() { return Tree(Leaf{}); }

  static Tree<A> node(Tree<A> t1, A x, Tree<A> t2) {
    return Tree(Node{std::make_shared<Tree<A>>(std::move(t1)), std::move(x),
                     std::make_shared<Tree<A>>(std::move(t2))});
  }

  // MANIPULATORS
  ~Tree() {
    std::vector<std::shared_ptr<Tree<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Tree<A> &_node) {
      if (std::holds_alternative<Node>(_node.v_)) {
        auto &_alt = std::get<Node>(_node.v_);
        if (_alt.t1) {
          _stack.push_back(std::move(_alt.t1));
        }
        if (_alt.t2) {
          _stack.push_back(std::move(_alt.t2));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

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
