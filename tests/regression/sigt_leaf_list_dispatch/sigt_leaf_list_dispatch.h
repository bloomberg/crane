#ifndef INCLUDED_SIGT_LEAF_LIST_DISPATCH
#define INCLUDED_SIGT_LEAF_LIST_DISPATCH

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A, typename P> struct SigT;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
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
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  P projT2() const {
    const auto &[x0, a1] = *this;
    return a1;
  }
};

/// A LIST is built by generically dispatching to another production's
/// result (mirroring how a grammar builds e.g. TREES ::= TREE TREES via a
/// generic `find_predicate_and_action`-style call whose return type is
/// production-dependent, hence erased to std::any), and consing that
/// generic result onto an accumulating list, then forwarding the whole list
/// to a concretely-typed top-level function. run's return type
/// domty (projT1 e) depends on the runtime witness e, so its call sites
/// only see std::any; the erased list is boxed as List<std::any>, while
/// wrap_list expects the concrete List<uint64_t>.
bool wrap_list(const List<uint64_t> &xs);
using domty = std::any;
using entry = SigT<uint64_t, std::function<domty(std::monostate)>>;

template <typename F1>
  requires std::is_invocable_r_v<domty, F1 &, std::monostate &>
entry mk(uint64_t p, F1 &&f) {
  return SigT<uint64_t, std::function<std::any(std::monostate)>>::existt(p, f);
}

domty run(const SigT<uint64_t, std::function<std::any(std::monostate)>> &e);
const entry entry_tree =
    mk(UINT64_C(1), [](std::monostate) { return UINT64_C(42); });
const entry entry_trees = mk(UINT64_C(0), [](std::monostate) {
  return List<std::any>::cons(run(entry_tree), List<std::any>::nil());
});
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_LEAF_LIST_DISPATCH
