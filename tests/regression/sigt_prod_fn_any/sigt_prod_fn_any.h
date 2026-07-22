#ifndef INCLUDED_SIGT_PROD_FN_ANY
#define INCLUDED_SIGT_PROD_FN_ANY

#include "crane_fn.h"
#include <any>
#include <functional>
#include <memory>
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
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

template <typename M>
concept SEM = requires {
  typename M::idx;
  typename M::sem;
};

template <SEM S> struct Make {
  using prod2 = std::pair<typename S::idx, List<typename S::idx>>;
  /// predicate_semty-analog: value-dependent function type -> std::any.
  using pred_ty = std::any;
  /// action_semty-analog: value-dependent function type -> std::any.
  using act_ty = std::any;
  /// production_semty-analog: a *pair* of the two erased function types, i.e.
  /// C++ std::pair<std::any, std::any>.
  using psem = std::pair<pred_ty, act_ty>;
  /// grammar_entry-analog.
  using entry = SigT<prod2, psem>;

  /// Store the predicate/action pair. The two lambdas are erased to std::any
  /// through the pair conversion — the fix's crane_erase_fn is NOT applied.
  template <typename F1, typename F2>
  static entry mk(typename S::idx a, F1 &&f, F2 &&g) {
    return SigT<prod2, psem>::existt(
        std::make_pair(a, List<typename S::idx>::nil()),
        std::make_pair(crane_erase_fn(f), crane_erase_fn(g)));
  }

  /// Look up + apply the predicate, exactly like Parser.v:113 if p vs' ....
  /// Applying just the predicate is enough to hit the crash: it is the first
  /// any_cast<std::function<...>> the parser performs. The action g stays in
  /// the stored pair so the payload keeps its product-of-erased-functions
  /// shape.
  template <typename F1>
  static bool run(const SigT<std::pair<typename S::idx, List<typename S::idx>>,
                             std::pair<std::any, std::any>> &e,
                  F1 &&arg) {
    const auto &[x0, a1] = e;
    const auto &[a, _x] = x0;
    const auto &[f, _x0] = std::any_cast<std::pair<std::any, std::any>>(a1);
    if (std::any_cast<bool>(
            std::any_cast<std::function<std::any(std::any)>>(f)(arg(a)))) {
      return true;
    } else {
      return false;
    }
  }
};

struct Inst {
  using idx = std::monostate;
  using sem = uint64_t;
};

using M = Make<Inst>;
const M::entry my_entry = M::mk(
    std::monostate{}, [](uint64_t n) { return n == UINT64_C(0); },
    [](uint64_t n) { return (n + 1); });
Inst::sem my_arg(std::monostate _x);
/// In Rocq this is true (predicate 0 =? 0 holds), and the extracted C++ now
/// returns true as well (before the fix it threw std::bad_any_cast).
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_PROD_FN_ANY
