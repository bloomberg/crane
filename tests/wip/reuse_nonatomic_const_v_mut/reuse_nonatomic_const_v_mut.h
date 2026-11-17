#pragma once

#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "obj.h"
#include "rc.h"
#include "small_vector.h"

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::rc<List<A>> l;
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
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? crane::make_rc<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  static List<A> cons_crane_reuse(crane::rc<List<A>> _tok, A a, List<A> l) {
    return List<A>(Cons{std::move(a), crane::make_rc_reusing<List<A>>(
                                          std::move(_tok), std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> crane::rc<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    crane::rc<List<A>> _cur = _next(v_mut());
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Under Reuse and NonAtomicRc, a local fixpoint whose list parameter is taken
/// by value matches on a field of a const auto & structured binding with
/// a0.v_mut(): "'this' argument to member function 'v_mut' has type 'const
/// tree', but function is not marked const".  Either flag alone is fine.
struct ReuseNonatomicConstVMut {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::rc<tree> a0;
      uint64_t a1;
      crane::rc<tree> a2;
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

    static tree node(crane::child_slot<tree> a0, uint64_t a1,
                     crane::child_slot<tree> a2) {
      return tree(Node{a0.take(), a1, a2.take()});
    }

    static tree node_crane_reuse(crane::rc<tree> _tok, tree a0, uint64_t a1,
                                 tree a2) {
      return tree(
          Node{crane::make_rc_reusing<tree>(std::move(_tok), std::move(a0)), a1,
               crane::make_rc<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<crane::rc<tree>> _stack = {};
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
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return f;
    } else {
      const auto &[a0, a1, a2] = std::get<typename tree::Node>(t0.v());
      return f0(*a0, tree_rect<T1>(f, f0, *a0), a1, *a2,
                tree_rect<T1>(f, f0, *a2));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t0) {
    return tree_rect<T1>(std::move(f), f0, t0);
  }

  static inline const uint64_t t = []() {
    return []() {
      List<bool> w;
      auto go = [](List<tree> l, const List<bool> &acc) -> List<bool> {
        // Loop replaces the tail recursion: each recursive call updates the
        // loop variables.
        List<bool> _loop_acc = acc;
        const List<tree> *_loop_l = &l;
        while (true) {
          if (std::holds_alternative<typename List<tree>::Nil>(_loop_l->v())) {
            return List<bool>::nil();
          } else {
            const auto &[a0, a1] =
                std::get<typename List<tree>::Cons>(_loop_l->v());
            const List<tree> &a1_value = *a1;
            _loop_acc = [&]() {
              if (std::holds_alternative<typename tree::Leaf>(a0.v_mut())) {
                if (List<uint64_t>::nil().template fold_left<bool>(
                        [](bool, uint64_t) { return true; }, true)) {
                  return _loop_acc;
                } else {
                  return List<bool>::nil();
                }
              } else {
                return _loop_acc;
              }
            }();
            _loop_l = &a1_value;
          }
        }
      };
      w = go(List<tree>::nil(), List<bool>::nil());
      return w.template fold_left<uint64_t>(
          [](uint64_t a,
             bool e) { return (a + (e ? UINT64_C(1) : UINT64_C(2))); },
          UINT64_C(1));
    }();
  }();
};
