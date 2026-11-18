#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f0, T1 a0) const {
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
        _loop_a0 = f0(std::move(_loop_a0), a1);
      }
    }
  }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Two branches producing function values of different C++ types, with no
/// common type spelled for the result (the pair-of-lambdas form in
/// branch_pairs_of_lambdas is fixed):
/// - t: in a fold_left step, one branch returns a composed let-lambda,
/// the other a plain lambda: "return type '(lambda ...)' must match
/// previous return type '(lambda ...)'".
/// - u: a class method (sz) in one if branch and a lambda from a match
/// in the other, as a constructor argument: "incompatible operand types
/// ('uint64_t (uint64_t)' and '(lambda ...)')".

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct BranchCallablesDistinctTypes {
  struct pt {
    uint64_t px;
    bool py;
  };

  static inline const uint64_t t = []() {
    return []() {
      crane::fn<pt(uint64_t)> w =
          List<bool>::cons(true, List<bool>::nil()).template fold_left<
              crane::fn<pt(uint64_t)>>(
              [](crane::fn<pt(uint64_t)>, bool e) {
                if (!(e)) {
                  crane::fn<pt(uint64_t)> cf =
                      [](uint64_t) { return pt{UINT64_C(1), true}; };
                  crane::fn<uint64_t(uint64_t)> cg =
                      [](uint64_t k) { return k; };
                  return [=, cf = std::move(cf), cg = std::move(cg)](uint64_t c) {
                    return cf(cg(c));
                  };
                } else {
                  return [](uint64_t) { return pt{UINT64_C(2), true}; };
                }
              },
              [](uint64_t) { return pt{UINT64_C(0), true}; });
      return (w(UINT64_C(0)).px + w(UINT64_C(3)).px);
    }();
  }();

  struct sz_nat {
    constexpr static uint64_t sz(uint64_t n) { return n; }
  };

  static_assert(Sz<sz_nat, uint64_t>);

  template <typename A> struct ptree {
    // TYPES
    struct PLeaf {};

    struct PNode {
      std::shared_ptr<ptree<A>> a0;
      A a1;
      std::shared_ptr<ptree<A>> a2;
    };

    using variant_t = std::variant<PLeaf, PNode>;

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
            if (std::holds_alternative<typename ptree<CraneU>::PLeaf>(
                    _other.v())) {
              return PLeaf{};
            } else {
              const auto &[a0, a1, a2] =
                  std::get<typename ptree<CraneU>::PNode>(_other.v());
              return PNode{
                  (a0 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a0))
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
                  (a2 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a2))
                      : nullptr)};
            }
          }()) {}

    static ptree<A> pleaf() { return ptree<A>(PLeaf{}); }

    static ptree<A> pnode(crane::shared_child_slot<ptree<A>> a0, A a1,
                          crane::shared_child_slot<ptree<A>> a2) {
      return ptree<A>(PNode{a0.take(), std::move(a1), a2.take()});
    }

    // MANIPULATORS
    ~ptree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<PLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<PNode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ptree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<PNode>(&_v)) {
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

    ptree(const ptree &) = default;
    ptree &operator=(const ptree &) = default;
    ptree(ptree &&) = default;
    ptree &operator=(ptree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 ptree_rect(T2 f0, F1 &&f1, const ptree<T1> &p) {
    if (std::holds_alternative<typename ptree<T1>::PLeaf>(p.v())) {
      return f0;
    } else {
      const auto &[a0, a1, a2] = std::get<typename ptree<T1>::PNode>(p.v());
      return f1(*a0, ptree_rect<T1, T2>(f0, f1, *a0), a1, *a2,
                ptree_rect<T1, T2>(f0, f1, *a2));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 ptree_rec(T2 f0, F1 &&f1, const ptree<T1> &p) {
    return ptree_rect<T1, T2>(std::move(f0), f1, p);
  }

  static ptree<crane::fn<uint64_t(uint64_t)>> f(bool b, List<uint64_t> l);
  static inline const uint64_t u = ([]() {
    auto &&_sv =
        f(false, List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()));
    if (std::holds_alternative<
            typename ptree<crane::fn<uint64_t(uint64_t)>>::PLeaf>(_sv.v())) {
      return UINT64_C(0);
    } else {
      const auto &[_, a1, _] =
          std::get<typename ptree<crane::fn<uint64_t(uint64_t)>>::PNode>(
              _sv.v());
      return a1(UINT64_C(7));
    }
  }() + []() {
    auto &&_sv0 = f(true, List<uint64_t>::nil());
    if (std::holds_alternative<
            typename ptree<crane::fn<uint64_t(uint64_t)>>::PLeaf>(_sv0.v())) {
      return UINT64_C(0);
    } else {
      const auto &[_, a10, _] =
          std::get<typename ptree<crane::fn<uint64_t(uint64_t)>>::PNode>(
              _sv0.v());
      return a10(UINT64_C(7));
    }
  }());
};
