#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
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

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A local fixpoint returning a function through a non-tail recursive call
/// (let rv := go r acc in if .. then (fun _ => Leaf) else rv), in a match
/// branch, called on a literal []: under CRANE_CHECK_IR=1 "closure escape:
/// the local fixpoint go escapes in its generated code but nowhere in Core".
/// The tail-call shapes in local_fix_returns_function and
/// local_fix_function_result_inlined are fixed.  Eta-expanded to the
/// function's argument, go r acc is a partial application, whose closure
/// holds go: escape analysis now counts one as an escape.
struct LocalFixNontailFunctionResult {
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

    static tree node(crane::shared_child_slot<tree> a0, uint64_t a1,
                     crane::shared_child_slot<tree> a2) {
      return tree(Node{a0.take(), a1, a2.take()});
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

  template <typename F1> static tree g(const tree &t0, F1 &&x0_) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      auto go_impl =
          [](auto &_self_go, List<tree> l,
             crane::fn<tree(crane::fn<uint64_t(uint64_t)>)> acc,
             crane::fn<uint64_t(uint64_t)> x0_0)
               -> tree {
            if (std::holds_alternative<typename List<tree>::Nil>(l.v_mut())) {
              return tree::leaf();
            } else {
              auto &[_, a10] = std::get<typename List<tree>::Cons>(l.v_mut());
              const List<tree> &a10_value = *a10;
              crane::fn<tree(crane::fn<uint64_t(uint64_t)>)> rv =
                  [=, a10_value = a10_value, acc = std::move(acc)](
                      crane::fn<uint64_t(uint64_t)> _pa0) {
                    return _self_go(_self_go, a10_value, std::move(acc), _pa0);
                  };
              if (UINT64_C(0) == UINT64_C(1)) {
                return tree::leaf();
              } else {
                return rv(std::move(x0_0));
              }
            }
          };
      List<tree> _lc1_l = List<tree>::nil();
      crane::fn<tree(crane::fn<uint64_t(uint64_t)>)> _lc1_acc =
          [](const crane::fn<uint64_t(uint64_t)> &) { return tree::leaf(); };
      crane::fn<uint64_t(uint64_t)> _lc1_x0_0 = x0_;
      return go_impl(go_impl, std::move(_lc1_l), std::move(_lc1_acc),
                     std::move(_lc1_x0_0));
    } else {
      return tree::leaf();
    }
  }

  static inline const bool t =
      (std::holds_alternative<typename tree::Leaf>(
           g(tree::leaf(), [](uint64_t x) { return x; }).v()) ? true : false);

  struct pt {
    uint64_t px;
    bool py;
  };

  /// Variants: the call in mutual fixpoints, through a second local fixpoint
  /// whose step returns its function accumulator, and with the outer
  /// fixpoint called inside the inner one's step.
  static List<pt> h6a(uint64_t n, const tree &x0_);
  static List<pt> h6b(uint64_t n, const tree &x0_);
  static List<pt> k1(uint64_t n, const tree &x0_);
  static inline const uint64_t t2 =
      h6a(UINT64_C(3), tree::leaf()).length() +
      k1(UINT64_C(2), tree::leaf()).length();
};
