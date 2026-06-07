#ifndef INCLUDED_MEM_SAFETY_PROBE22
#define INCLUDED_MEM_SAFETY_PROBE22

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
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
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
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

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          _drain(_cur->v_mut());
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
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      std::decay_t<T1> _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          _f.a1, std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                     std::move(_f.a2), std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0,
                     const tree &t) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      std::decay_t<T1> _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), std::move(_f.a2),
                                          _f.a1, std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                     std::move(_f.a2), std::move(_f._result));
      }
    }
    return _result;
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
  static tree tree_map(F0 &&f,
                       const tree &t) { /// _Enter: captures varying parameters
                                        /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _After_Node: saves [a0, a1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0;
      uint64_t a1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      tree _result;
      uint64_t a1;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    tree _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_map: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = tree::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), f(a1)});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result = tree::node(std::move(_result), _f.a1, std::move(_f._result));
      }
    }
    return _result;
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
