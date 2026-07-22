#ifndef INCLUDED_SIGT_FN_ANY
#define INCLUDED_SIGT_FN_ANY

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
  /// production-analog: an index plus a list of indices.
  using prod2 = std::pair<typename S::idx, List<typename S::idx>>;
  /// predicate_semty-analog: a value-dependent function type. The
  /// let (a, _) := p blocks reduction for a variable p, so Crane must erase
  /// pred_ty p to std::any — exactly like predicate_semty in Defs.v.
  using pred_ty = std::any;
  /// grammar_entry-analog: a dependent pair carrying the function payload.
  using entry = SigT<prod2, pred_ty>;

  /// Build an entry from a concrete index and a predicate lambda.
  /// The lambda is stored at the erased type pred_ty (a, []) = std::any.
  template <typename F1> static entry mk(typename S::idx a, F1 &&f) {
    return SigT<prod2, std::any>::existt(
        std::make_pair(a, List<typename S::idx>::nil()), f);
  }

  /// Look up + apply: destructure the entry and apply the stored predicate.
  /// Here the projected f has C++ static type std::any, so Crane emits
  /// any_cast<std::function<...>>(f)(...) — the failing cast.
  template <typename F1>
  static bool run(const SigT<std::pair<typename S::idx, List<typename S::idx>>,
                             std::any> &e,
                  F1 &&arg) {
    const auto &[x0, a1] = e;
    const auto &[a, _x] = x0;
    if (std::any_cast<bool>(
            std::any_cast<std::function<std::any(std::any)>>(a1)(arg(a)))) {
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
const M::entry my_entry =
    M::mk(std::monostate{}, [](uint64_t n) { return n == UINT64_C(0); });
Inst::sem my_arg(std::monostate _x);
/// In Rocq this evaluates to true ((fun n => n =? 0) 0). In C++ the extracted
/// code throws std::bad_any_cast when called. Kept as a function (not a value)
/// so the C++ test driver can invoke it under try/catch rather than crashing at
/// static-initialization time.
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_FN_ANY
