#ifndef INCLUDED_MEM_SAFETY_PROBE22
#define INCLUDED_MEM_SAFETY_PROBE22

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
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
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
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
      std::unique_ptr<tree> a0;
      uint64_t a1;
      std::unique_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
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
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
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
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return f0(*a0, tree_rec<T1>(f, f0, *a0), a1, *a2,
                tree_rec<T1>(f, f0, *a2));
    }
  }

  static uint64_t tree_sum(const tree &t);
  /// TEST 1: Two recursive calls on CHILDREN, but the
  /// function takes tree by value because it also returns/stores it.
  static std::pair<tree, uint64_t> sum_and_rebuild(const tree &t);
  static inline const uint64_t test_sum_and_rebuild =
      sum_and_rebuild(
          tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                     UINT64_C(5),
                     tree::node(tree::leaf(), UINT64_C(2), tree::leaf())))
          .second;
  /// TEST 2: Function that recurses on children AND stores result
  /// in constructor, forcing the tree to be owned.
  static tree double_tree(const tree &t);
  static inline const uint64_t test_double_tree =
      tree_sum(double_tree(tree::node(
          tree::node(tree::leaf(), UINT64_C(3), tree::leaf()), UINT64_C(5),
          tree::node(tree::leaf(), UINT64_C(7), tree::leaf()))));
  /// TEST 3: Two recursive calls with child + value in result.
  static uint64_t weighted_sum(const tree &t, uint64_t w);
  static inline const uint64_t test_weighted_sum = weighted_sum(
      tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                 UINT64_C(5),
                 tree::node(tree::leaf(), UINT64_C(7), tree::leaf())),
      UINT64_C(1));
  /// TEST 4: Function with constructed-tree recursive calls.
  static uint64_t split_sum(const tree &t, uint64_t n);
  static inline const uint64_t test_split_sum = split_sum(
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(1));

  /// TEST 5: Tree map with two recursive calls on children.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static tree tree_map(F0 &&f, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return tree::leaf();
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
      return tree::node(tree_map(f, *a0), f(a1), tree_map(f, *a2));
    }
  }

  static inline const uint64_t test_tree_map = tree_sum(tree_map(
      [](uint64_t n) { return (n + UINT64_C(10)); },
      tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                 UINT64_C(2),
                 tree::node(tree::leaf(), UINT64_C(3), tree::leaf()))));
  /// TEST 6: Mirror tree (swap children). Two recursive calls.
  static tree mirror(const tree &t);
  static inline const uint64_t test_mirror = tree_sum(mirror(tree::node(
      tree::node(tree::leaf(), UINT64_C(1), tree::leaf()), UINT64_C(2),
      tree::node(tree::leaf(), UINT64_C(3), tree::leaf()))));
  /// TEST 7: Insert into BST (non-pointer-safe because constructed tree
  /// in recursive call).
  static tree insert(const tree &t, uint64_t x);
  static tree insert_all(tree t, const List<uint64_t> &xs);
  static inline const uint64_t test_insert = tree_sum(
      insert_all(tree::leaf(),
                 List<uint64_t>::cons(
                     UINT64_C(5),
                     List<uint64_t>::cons(
                         UINT64_C(3),
                         List<uint64_t>::cons(
                             UINT64_C(7),
                             List<uint64_t>::cons(
                                 UINT64_C(1),
                                 List<uint64_t>::cons(
                                     UINT64_C(9), List<uint64_t>::nil())))))));
  /// TEST 8: Deep tree transformation with two recursive calls.
  static tree label_depth(const tree &t, uint64_t d);
  static inline const uint64_t test_label_depth = tree_sum(label_depth(
      tree::node(tree::node(tree::leaf(), UINT64_C(0), tree::leaf()),
                 UINT64_C(0),
                 tree::node(tree::leaf(), UINT64_C(0), tree::leaf())),
      UINT64_C(1)));
};

#endif // INCLUDED_MEM_SAFETY_PROBE22
