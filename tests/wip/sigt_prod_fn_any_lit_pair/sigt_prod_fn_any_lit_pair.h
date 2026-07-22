#ifndef INCLUDED_SIGT_PROD_FN_ANY_LIT_PAIR
#define INCLUDED_SIGT_PROD_FN_ANY_LIT_PAIR

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

/// Same shape as sigt_prod_fn_any_lit (grammar entry = sigma-type pairing a
/// production with an erased predicate/action pair), but here the
/// predicate/action *domain* is itself a concrete pair `sem a * unit`
/// (mirroring symbols_semty ys := symbol_semty y * symbols_semty ys' in
/// theories/Parser/Defs.v), so the inline generic lambda body must
/// structurally destructure its argument via `let (v, _x) := tup`.
template <SEM S> struct Make {
  using dom = std::pair<std::any, std::monostate>;
  using prod2 = std::pair<typename S::idx, List<typename S::idx>>;
  using pred_ty = std::any;
  using act_ty = std::any;
  using psem = std::pair<pred_ty, act_ty>;
  using entry = SigT<prod2, psem>;

  static entry mk_entry(typename S::idx a) {
    return SigT<prod2, psem>::existt(
        std::make_pair(a, List<typename S::idx>::nil()),
        std::make_pair(crane_erase_fn([](const auto &tup) {
                         const auto &[_x, _x0] = tup;
                         return true;
                       }),
                       crane_erase_fn([](const auto &tup) {
                         const auto &[_x, _x0] = tup;
                         return true;
                       })));
  }

  template <typename F1>
  static bool run(const SigT<std::pair<typename S::idx, List<typename S::idx>>,
                             std::pair<std::any, std::any>> &e,
                  F1 &&arg) {
    const auto &[x0, a1] = e;
    const auto &[a, _x] = x0;
    const auto &[f, _x0] = std::any_cast<std::pair<std::any, std::any>>(a1);
    if (std::any_cast<bool>(std::any_cast<std::function<std::any(std::any)>>(f)(
            std::make_pair(std::any(std::any(arg(a))),
                           std::any(std::any(std::monostate{})))))) {
      return true;
    } else {
      return false;
    }
  }
};

struct Inst {
  using idx = std::monostate;
  using sem = bool;
};

using M = Make<Inst>;
const M::entry my_entry = M::mk_entry(std::monostate{});
Inst::sem my_arg(std::monostate _x);
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_PROD_FN_ANY_LIT_PAIR
