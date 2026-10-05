#ifndef INCLUDED_LOOPIFY_MORE_TREES
#define INCLUDED_LOOPIFY_MORE_TREES

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
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

  List<A> app(List<A> m) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct LoopifyMoreTrees {
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

  static tree mirror(const tree &t);
  static bool same_shape(const tree &t1, const tree &t2);
  static List<uint64_t> tree_to_list(const tree &t);
  static bool mirror_equal(const tree &t);
  static uint64_t count_nodes(const tree &t);
  static tree tree_max(tree t1, tree t2);
  static uint64_t sum_of_max_branches(const tree &t);
  static tree insert_bst(uint64_t x, const tree &t);
  static tree build_bst(const List<uint64_t> &l);
  static List<uint64_t> append_lists(const List<uint64_t> &l1,
                                     List<uint64_t> l2);
  static List<uint64_t> flatten(const List<List<uint64_t>> &ll);
  static List<List<uint64_t>> map_tree_to_list(const List<tree> &lt);
  static List<tree> tree_children(const tree &t);
  static List<tree> append_trees(const List<tree> &l1, List<tree> l2);
  static List<tree> concat_map_children(const List<tree> &lt);
  static List<List<uint64_t>> tree_levels_fuel(uint64_t fuel,
                                               const List<tree> &level);
  static List<List<uint64_t>> tree_levels(const tree &t);
};

#endif // INCLUDED_LOOPIFY_MORE_TREES
