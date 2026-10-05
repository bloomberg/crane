#ifndef INCLUDED_MEM_SAFETY_PROBE22
#define INCLUDED_MEM_SAFETY_PROBE22

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

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
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const tree *t;
    };

    /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Node_1 {
      T1 _tmp2;
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0,
                     const tree &t) { /// CraneEnter: captures varying
                                      /// parameters for each recursive call.

    struct CraneEnter {
      const tree *t;
    };

    /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Node_1 {
      T1 _tmp2;
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_rec: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
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
  static constexpr uint64_t test_double_tree = UINT64_C(30);
  /// TEST 3: Two recursive calls with child + value in result.
  static uint64_t weighted_sum(const tree &t, uint64_t w);
  static constexpr uint64_t test_weighted_sum = UINT64_C(25);
  /// TEST 4: Function with constructed-tree recursive calls.
  static uint64_t split_sum(const tree &t, uint64_t n);
  static constexpr uint64_t test_split_sum = UINT64_C(22);

  /// TEST 5: Tree map with two recursive calls on children.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static tree tree_map(F0 &&f,
                       const tree &t) { /// CraneEnter: captures varying
                                        /// parameters for each recursive call.

    struct CraneEnter {
      const tree *t;
    };

    /// CraneCont_Node: saves [a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      uint64_t a1;
      const tree *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2, a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node_1 {
      tree _tmp2;
      uint64_t a1;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    tree _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_map: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = tree::leaf();
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_Node>(_frame));
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _stack.emplace_back(CraneCont_Node_1{std::move(_result), a1});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(std::get<CraneCont_Node_1>(_frame));
        uint64_t a1 = _f.a1;
        _result = tree::node(std::move(_f._tmp2), f(a1), std::move(_result));
      }
    }
    return _result;
  }

  static constexpr uint64_t test_tree_map = UINT64_C(36);
  /// TEST 6: Mirror tree (swap children). Two recursive calls.
  static tree mirror(const tree &t);
  static constexpr uint64_t test_mirror = UINT64_C(6);
  /// TEST 7: Insert into BST (non-pointer-safe because constructed tree
  /// in recursive call).
  static tree insert(const tree &t, uint64_t x);
  static tree insert_all(tree t, const List<uint64_t> &xs);
  static constexpr uint64_t test_insert = UINT64_C(25);
  /// TEST 8: Deep tree transformation with two recursive calls.
  static tree label_depth(const tree &t, uint64_t d);
  static constexpr uint64_t test_label_depth = UINT64_C(5);
};

#endif // INCLUDED_MEM_SAFETY_PROBE22
