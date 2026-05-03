#ifndef INCLUDED_MEM_SAFETY_PROBE22
#define INCLUDED_MEM_SAFETY_PROBE22

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
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

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct MemSafetyProbe22 {
  /// Probe 22: Owned-parameter loopification with continuation frames.
  ///
  /// Attack vector: When a recursive function takes a value-type tree
  /// by value (owned, not pointer-safe), the loopifier uses v_mut()
  /// for the match and optimize_frame_push_args can std::move children
  /// in _Enter frames. If continuation frames (_After) store raw pointers
  /// to OTHER children, those pointers dangle when the local tree goes
  /// out of scope at the end of the handler block.
  ///
  /// Key: the recursive call must take a DIFFERENT tree (not the original
  /// parameter) so the parameter is not pointer-safe.
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> d_a0;
      unsigned int d_a1;
      std::unique_ptr<tree> d_a2;
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

    tree(const tree &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    tree(tree &&_other) : d_v_(std::move(_other.d_v_)) {}

    tree &operator=(const tree &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->d_v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->d_v_ =
              Node{_alt.d_a0 ? std::make_unique<tree>() : nullptr, _alt.d_a1,
                   _alt.d_a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->d_v_);
          if (_alt.d_a0) {
            _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
          }
          if (_alt.d_a2) {
            _stack.push_back({_alt.d_a2.get(), _dst_alt.d_a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, unsigned int a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), std::move(a1),
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.d_v_)) {
          auto &_alt = std::get<Node>(_node.d_v_);
          if (_alt.d_a0) {
            _stack.push_back(std::move(_alt.d_a0));
          }
          if (_alt.d_a2) {
            _stack.push_back(std::move(_alt.d_a2));
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

    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rect(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rect<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rect<T1>(f, f0, *(d_a2)));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                   tree &, T1 &>
  static T1 tree_rec(const T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return f0(*(d_a0), tree_rec<T1>(f, f0, *(d_a0)), d_a1, *(d_a2),
                tree_rec<T1>(f, f0, *(d_a2)));
    }
  }

  static unsigned int tree_sum(const tree &t);
  /// TEST 1: Two recursive calls on CHILDREN, but the
  /// function takes tree by value because it also returns/stores it.
  static std::pair<tree, unsigned int> sum_and_rebuild(const tree &t);
  static inline const unsigned int test_sum_and_rebuild =
      sum_and_rebuild(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 5u,
                                 tree::node(tree::leaf(), 2u, tree::leaf())))
          .second;
  /// TEST 2: Function that recurses on children AND stores result
  /// in constructor, forcing the tree to be owned.
  static tree double_tree(const tree &t);
  static inline const unsigned int test_double_tree = tree_sum(
      double_tree(tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 5u,
                             tree::node(tree::leaf(), 7u, tree::leaf()))));
  /// TEST 3: Two recursive calls with child + value in result.
  static unsigned int weighted_sum(const tree &t, const unsigned int w);
  static inline const unsigned int test_weighted_sum =
      weighted_sum(tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 5u,
                              tree::node(tree::leaf(), 7u, tree::leaf())),
                   1u);
  /// TEST 4: Function with constructed-tree recursive calls.
  static unsigned int split_sum(const tree &t, const unsigned int n);
  static inline const unsigned int test_split_sum =
      split_sum(tree::node(tree::leaf(), 10u, tree::leaf()), 1u);

  /// TEST 5: Tree map with two recursive calls on children.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static tree tree_map(F0 &&f, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return tree::leaf();
    } else {
      const auto &[d_a0, d_a1, d_a2] = std::get<typename tree::Node>(t.v());
      return tree::node(tree_map(f, *(d_a0)), f(d_a1), tree_map(f, *(d_a2)));
    }
  }

  static inline const unsigned int test_tree_map = tree_sum(
      tree_map([](const unsigned int n) { return (n + 10u); },
               tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                          tree::node(tree::leaf(), 3u, tree::leaf()))));
  /// TEST 6: Mirror tree (swap children). Two recursive calls.
  static tree mirror(const tree &t);
  static inline const unsigned int test_mirror =
      tree_sum(mirror(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                                 tree::node(tree::leaf(), 3u, tree::leaf()))));
  /// TEST 7: Insert into BST (non-pointer-safe because constructed tree
  /// in recursive call).
  static tree insert(const tree &t, const unsigned int x);
  static tree insert_all(tree t, const List<unsigned int> &xs);
  static inline const unsigned int test_insert = tree_sum(insert_all(
      tree::leaf(),
      List<unsigned int>::cons(
          5u, List<unsigned int>::cons(
                  3u, List<unsigned int>::cons(
                          7u, List<unsigned int>::cons(
                                  1u, List<unsigned int>::cons(
                                          9u, List<unsigned int>::nil())))))));
  /// TEST 8: Deep tree transformation with two recursive calls.
  static tree label_depth(const tree &t, const unsigned int d);
  static inline const unsigned int test_label_depth = tree_sum(
      label_depth(tree::node(tree::node(tree::leaf(), 0u, tree::leaf()), 0u,
                             tree::node(tree::leaf(), 0u, tree::leaf())),
                  1u));
};

#endif // INCLUDED_MEM_SAFETY_PROBE22
