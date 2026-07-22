#ifndef INCLUDED_SIGT_LEAF_LIST_DISPATCH
#define INCLUDED_SIGT_LEAF_LIST_DISPATCH

#include <any>
#include <functional>
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

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
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
