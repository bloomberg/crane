#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Ascii;
struct String;

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
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, crane::shared_child_slot<String> a1) {
    return String(String0{std::move(a0), a1.take()});
  }

  // MANIPULATORS
  ~String() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<String> {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<String> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) = default;
  String &operator=(String &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated programs, shrunk by ephyra and reduced by
/// hand.
///
/// A function type behind a definition (st A := nat -> A * nat) was
/// spelled two ways: unfolded, a function of the arrows it hides, at some
/// sites, and kept, st<A>, at others.  Where the two met the C++ did not
/// compile: a parameter typed nat * nat -> st Z passed on from a match
/// ("no viable conversion from 'const fn<st<int64_t> (pair)>' to
/// 'fn<pair<int64_t,uint64_t> (pair, uint64_t)>'"), a composed let-lambda
/// returning st bool, and a local fixpoint over list (st bool).
struct FunctionAliasSpelling {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> l;
      uint64_t v_1;
      std::shared_ptr<tree> r;
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

    static tree node(crane::shared_child_slot<tree> l, uint64_t v_1,
                     crane::shared_child_slot<tree> r) {
      return tree(Node{l.take(), v_1, r.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->l && _alt->l.use_count() == 1) ||
              (_alt->r && _alt->r.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r && _alt->r.use_count() == 1) {
            _stack.push_back(std::move(_alt->r));
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
  static T1 tree_rect(T1 f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[l0, v_1, r0] = std::get<typename tree::Node>(t.v());
      return f0(*l0, tree_rect<T1>(f, f0, *l0), v_1, *r0,
                tree_rect<T1>(f, f0, *r0));
    }
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  template <typename a> using st = crane::fn<std::pair<a, uint64_t>(uint64_t)>;

  template <typename T1> static st<T1> sret(T1 a) {
    return [=, a = std::move(a)](uint64_t s) { return std::make_pair(a, s); };
  }

  static tree
  g2(const tree &t,
     const crane::fn<st<int64_t>(std::pair<uint64_t, uint64_t>)> &a);
  /// g2 with its parameter observed at the leaf.
  static int64_t
  g2z(const tree &t,
      const crane::fn<st<int64_t>(std::pair<uint64_t, uint64_t>)> &a);
  static inline const tree t1 = g2(
      tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                 UINT64_C(0), tree::leaf()),
      [](std::pair<uint64_t, uint64_t>) { return sret<int64_t>(INT64_C(5)); });
  static inline const bool t1_leaf =
      (std::holds_alternative<typename tree::Leaf>(t1.v()) ? true : false);
  static inline const int64_t z1 = g2z(
      tree::node(tree::leaf(), UINT64_C(0), tree::leaf()),
      [](std::pair<uint64_t, uint64_t>) { return sret<int64_t>(INT64_C(5)); });
  static inline const int64_t z2 = g2z(
      tree::node(tree::node(tree::leaf(), UINT64_C(0), tree::leaf()),
                 UINT64_C(1), tree::leaf()),
      [](std::pair<uint64_t, uint64_t>) { return sret<int64_t>(INT64_C(5)); });
  static st<bool> sf2(st<bool> a6, const List<uint64_t> &x0_);
  static inline const bool b2 =
      sf2(sret<bool>(true),
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())))(
          UINT64_C(0))
          .first;
  static inline const uint64_t n2 =
      sf2(sret<bool>(false), List<uint64_t>::nil())(UINT64_C(4)).second;
  static inline const std::optional<bool> f3 = []() {
    auto go =
        [](const List<st<bool>> &l, std::optional<bool> acc) -> std::optional<
            bool> {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          std::optional<bool> _loop_acc = acc;
          const List<st<bool>> *_loop_l = &l;
          while (true) {
            if (std::holds_alternative<typename List<st<bool>>::Nil>(
                    _loop_l->v())) {
              return _loop_acc;
            } else {
              const auto &[a0, a1] =
                  std::get<typename List<st<bool>>::Cons>(_loop_l->v());
              _loop_acc = std::make_optional<bool>(a0(UINT64_C(0)).first);
              _loop_l = crane_raw(a1);
            }
          }
        };
    return go(List<st<bool>>::cons(
        sret<bool>(true),
        List<st<bool>>::cons(sret<bool>(true), List<st<bool>>::nil())),
              std::optional<bool>());
  }();
};
