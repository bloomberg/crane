#pragma once

#include "crane_fn.h"
#include "crane_variant.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "shared_block.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <stdexcept>
#include <utility>

template <typename A> struct List;

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::shared_box<List<A>> l;
  };

  using variant_t = crane::shared_variant<Nil, Cons>;

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
      : v_([&]() -> variant_t {
          if (crane::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? crane::shared_box<List<A>>::make(
                         crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))});
  }

  static List<A> cons_crane_reuse(List<A> _tok, A a, List<A> l) {
    auto _alt =
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))};
    if (_tok.v_.try_reuse(std::move(_alt))) {
      return _tok;
    }
    return List<A>(Cons{std::move(_alt)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// Memory safety: at run time UBSan reports "reference binding to null pointer
/// of type 'const tree'" (abort). t_5 applies the class method sz to a match on
/// a tree built from a match on a record update, whose Node branch re-matches
/// its right subtree and stores it again.

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct NestedTreeMatchNullRef {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      crane::shared_box<tree> a2;
    };

    using variant_t = crane::shared_variant<Leaf, Node>;

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
      return tree(Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))});
    }

    static tree node_crane_reuse(tree _tok, tree a0, uint64_t a1, tree a2) {
      auto _alt = Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))};
      if (_tok.v_.try_reuse(std::move(_alt))) {
        return _tok;
      }
      return tree(Node{std::move(_alt)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t tree_obs() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_obs: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_obs_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_obs_in_Node_2 {
        uint64_t a1;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_obs_in_Node,
                                  _after_tree_obs_in_Node_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(1);
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_obs_in_Node{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (crane::holds_alternative<_after_tree_obs_in_Node>(_popped)) {
          auto _f = std::move(crane::get<_after_tree_obs_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_obs_in_Node_2{a1, _result});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(crane::get<_after_tree_obs_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          auto _once1 = _f._tmp2 * UINT64_C(7) + a1 + _result * UINT64_C(3);
          _result = (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
      return this->template tree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_rect_in_Node {
        crane::shared_box<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_rect_in_Node_2 {
        crane::shared_box<tree> a0;
        uint64_t a1;
        const tree *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                  _after_tree_rect_in_Node_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = crane::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_rect_in_Node{a0, a1,
                                                         crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (crane::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(crane::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), a1, &a2,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(crane::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          crane::shared_box<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct sz_tree {
    static uint64_t sz(tree a0) { return a0.tree_obs(); }
  };

  static_assert(Sz<sz_tree, tree>);

  template <typename A> struct ptree {
    // TYPES
    struct PLeaf {};

    struct PNode {
      crane::shared_box<ptree<A>> a0;
      A a1;
      crane::shared_box<ptree<A>> a2;
    };

    using variant_t = crane::shared_variant<PLeaf, PNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ptree() {}

    explicit ptree(PLeaf _v) : v_(_v) {}

    explicit ptree(PNode _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    ptree(const ptree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (crane::holds_alternative<typename ptree<CraneU>::PLeaf>(
                    _other.v())) {
              return PLeaf{};
            } else {
              const auto &[a0, a1, a2] =
                  crane::get<typename ptree<CraneU>::PNode>(_other.v());
              return PNode{
                  (a0 ? crane::shared_box<ptree<A>>::make(
                            crane_convert<ptree<A>>(*a0))
                      : nullptr),
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a1);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a2 ? crane::shared_box<ptree<A>>::make(
                            crane_convert<ptree<A>>(*a2))
                      : nullptr)};
            }
          }()) {}

    static ptree<A> pleaf() { return ptree<A>(PLeaf{}); }

    static ptree<A> pnode(ptree<A> a0, A a1, ptree<A> a2) {
      return ptree<A>(
          PNode{crane::shared_box<ptree<A>>::make(std::move(a0)), std::move(a1),
                crane::shared_box<ptree<A>>::make(std::move(a2))});
    }

    static ptree<A> pnode_crane_reuse(ptree<A> _tok, ptree<A> a0, A a1,
                                      ptree<A> a2) {
      auto _alt =
          PNode{crane::shared_box<ptree<A>>::make(std::move(a0)), std::move(a1),
                crane::shared_box<ptree<A>>::make(std::move(a2))};
      if (_tok.v_.try_reuse(std::move(_alt))) {
        return _tok;
      }
      return ptree<A>(PNode{std::move(_alt)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1> T1 ptree_rec(T1 f, F1 &&f0) const {
      return this->template ptree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 ptree_rect(T1 f, F1 &&f0) const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of ptree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
      };

      struct _after_ptree_rect_in_PNode {
        crane::shared_box<ptree<A>> a0;
        A a1;
        const ptree<A> *a2;
      };

      struct _after_ptree_rect_in_PNode_2 {
        crane::shared_box<ptree<A>> a0;
        A a1;
        const ptree<A> *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_ptree_rect_in_PNode,
                                  _after_ptree_rect_in_PNode_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (crane::holds_alternative<_call>(_popped)) {
          auto _f = std::move(crane::get<_call>(_popped));
          _stack.pop_back();
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (crane::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] =
                crane::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(
                _after_ptree_rect_in_PNode{a0, a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                crane::holds_alternative<_after_ptree_rect_in_PNode>(_popped)) {
          auto _f = std::move(crane::get<_after_ptree_rect_in_PNode>(_popped));
          _stack.pop_back();
          crane::shared_box<ptree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(_after_ptree_rect_in_PNode_2{
              std::move(a0), std::move(a1), &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f =
              std::move(crane::get<_after_ptree_rect_in_PNode_2>(_popped));
          _stack.pop_back();
          crane::shared_box<ptree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct stream {
    // TYPES
    template <typename CraneS0 = stream> struct SCons_ {
      uint64_t a0;
      CraneS0 a1;
    };

    using SCons = SCons_<>;
    using variant_t = std::variant<SCons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(SCons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream scons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  template <typename a> using st = crane::fn<std::pair<a, uint64_t>(uint64_t)>;

  struct r3 {
    uint64_t ra;
    List<uint64_t> rb;
    bool rc;
  };

  static inline const uint64_t t_5 = sz_tree::sz([]() {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto k =
        crane::immortal(tree::node(tree::leaf(), UINT64_C(0), tree::leaf()));
    auto _cs = []() {
      r3 rr23 = r3{UINT64_C(0), List<uint64_t>::nil(), true};
      return r3{rr23.ra, List<uint64_t>::nil(), !(rr23.rc)};
    }();
    uint64_t ma25 = std::move(_cs).ra;
    crane::obj _x = std::move(_cs).rb;
    crane::obj _x0 = std::move(_cs).rc;
    tree tr30 = tree::node(tree::leaf(), ma25, tree::leaf());
    return tree::node(
        (crane::holds_alternative<typename tree::Leaf>(tr30.v()) ? tree::leaf()
                                                                 : k),
        UINT64_C(0), tr30);
  }());
};
