#pragma once

#include "crane_fn.h"
#include "crane_variant.h"
#include "obj.h"
#include "shared_block.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>

template <typename A> struct List;

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

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = crane::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

struct LoopifySharedVariantMovedRead {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> l;
      uint64_t v_1;
      crane::shared_box<tree> r;
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

    static tree node(tree l, uint64_t v_1, tree r) {
      return tree(Node{crane::shared_box<tree>::make(std::move(l)), v_1,
                       crane::shared_box<tree>::make(std::move(r))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    // Explicit stack replaces the non-tail recursion of tree_rect: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const tree *t;
    };

    struct _after_tree_rect_in_Node {
      crane::shared_box<tree> l0;
      uint64_t v_1;
      const tree *r0;
    };

    struct _after_tree_rect_in_Node_2 {
      crane::shared_box<tree> l0;
      uint64_t v_1;
      const tree *r0;
      T1 _tmp2;
    };

    using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                _after_tree_rect_in_Node_2>;
    T1 _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{&t});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (crane::holds_alternative<_call>(_popped)) {
        auto _f = std::move(crane::get<_call>(_popped));
        _stack.pop_back();
        const tree &t = *_f.t;
        if (crane::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[l0, v_1, r0] = crane::get<typename tree::Node>(t.v());
          _stack.emplace_back(_after_tree_rect_in_Node{l0, v_1, crane_raw(r0)});
          _stack.emplace_back(_call{crane_raw(l0)});
        }
      } else if (crane::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
        auto _f = std::move(crane::get<_after_tree_rect_in_Node>(_popped));
        _stack.pop_back();
        crane::shared_box<tree> l0 = std::move(_f.l0);
        uint64_t v_1 = _f.v_1;
        const tree &r0 = *_f.r0;
        _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(l0), v_1, &r0,
                                                       std::move(_result)});
        _stack.emplace_back(_call{&r0});
      } else {
        auto _f = std::move(crane::get<_after_tree_rect_in_Node_2>(_popped));
        _stack.pop_back();
        crane::shared_box<tree> l0 = std::move(_f.l0);
        uint64_t v_1 = _f.v_1;
        const tree &r0 = *_f.r0;
        _result = f0(*l0, std::move(_f._tmp2), v_1, r0, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static tree g(const List<uint64_t> &l);
  static uint64_t size(const tree &t);
  static inline const uint64_t result = size(g(List<uint64_t>::cons(
      UINT64_C(1),
      List<uint64_t>::cons(
          UINT64_C(2),
          List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))));
};
