#ifndef INCLUDED_ACTION_CONTAINER_CAST
#define INCLUDED_ACTION_CONTAINER_CAST

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <deque>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

enum class Unit;
enum class Bool0;
struct Nat;
template <typename A, typename B> struct Prod;
template <typename A, typename P> struct SigT;
struct R;
enum class Nonterminal;
struct Symbol;
using symbol_semty = crane::obj;
using predicate_semty = crane::obj;
using action_semty = crane::obj;
enum class Unit { TT };
enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A, typename B> struct Prod {
  // DATA
  A a0;
  B a1;

  // ACCESSORS
  Prod<A, B> clone() const { return {a0, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator Prod<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const B &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static Prod<A, B> pair(A a0, B a1) { return {std::move(a0), std::move(a1)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct R {
  // TYPES
  struct RArr {
    std::shared_ptr<std::deque<R>> a0;
  };

  struct RNum {
    Nat a0;
  };

  using variant_t = std::variant<RArr, RNum>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  R() {}

  explicit R(RArr _v) : v_(std::move(_v)) {}

  explicit R(RNum _v) : v_(std::move(_v)) {}

  static R rarr(std::deque<R> a0) {
    return R(RArr{std::make_shared<std::deque<R>>(std::move(a0))});
  }

  static R rnum(Nat a0) { return R(RNum{std::move(a0)}); }

  // MANIPULATORS
  ~R() {
    if (std::holds_alternative<RNum>(v_mut())) {
      return;
    }
    crane::small_vector<std::shared_ptr<R>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<RArr>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          for (auto &_elem : *_alt->a0) {
            _stack.push_back(std::make_shared<R>(std::move(_elem)));
          }
          _alt->a0.reset();
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

  R(const R &) = default;
  R &operator=(const R &) = default;
  R(R &&) = default;
  R &operator=(R &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};
enum class Nonterminal { NARR, NVAL };

struct Symbol {
  // TYPES
  struct T {};

  struct NT {
    Nonterminal a0;
  };

  using variant_t = std::variant<T, NT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Symbol() {}

  explicit Symbol(T _v) : v_(_v) {}

  explicit Symbol(NT _v) : v_(std::move(_v)) {}

  static Symbol t() { return Symbol(T{}); }

  static Symbol nt(Nonterminal a0) { return Symbol(NT{a0}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

using production = Prod<Nonterminal, std::deque<Symbol>>;
using production_semty = Prod<predicate_semty, action_semty>;
using grammar_entry = SigT<production, production_semty>;
/// Minimal grammar isolating the container conversion:
/// - NArr ->         (nil):  builds the empty list R -> erased deque<any>
/// - NVal -> NT NArr   (JList): applies RArr to that erased list leaf.
const std::deque<grammar_entry> entries =
    [](auto _a0, auto _a1) {
      _a1.push_front(_a0);
      return _a1;
    }(SigT<Prod<Nonterminal, std::deque<Symbol>>,
           Prod<crane::obj, crane::obj>>::
          existt(Prod<Nonterminal, std::deque<Symbol>>::pair(
                     Nonterminal::NARR, std::deque<Symbol>{}),
                 Prod<crane::obj, crane::obj>::pair(
                     crane_erase_fn(
                         [](const crane::obj &) { return Bool0::TRUE_; }),
                     crane_erase_fn([](const crane::obj &) {
                       return std::deque<crane::obj>{};
                     }))),
      [](auto _a0, auto _a1) {
        _a1.push_front(_a0);
        return _a1;
      }(SigT<Prod<Nonterminal, std::deque<Symbol>>,
             Prod<crane::obj, crane::obj>>::
            existt(Prod<Nonterminal, std::deque<Symbol>>::pair(
                       Nonterminal::NVAL,
                       [](auto _a0, auto _a1) {
                         _a1.push_front(_a0);
                         return _a1;
                       }(Symbol::nt(Nonterminal::NARR), std::deque<Symbol>{})),
                   Prod<crane::obj, crane::obj>::pair(
                       crane_erase_fn(
                           [](const crane::obj &) { return Bool0::TRUE_; }),
                       crane_erase_fn([](const crane::obj &_any_ss) {
                         Prod<symbol_semty, Unit> ss =
                             crane::any_cast<Prod<symbol_semty, Unit>>(_any_ss);
                         const auto &[a0, a1] = ss;
                         return R::rarr(crane_container_cast<std::deque<R>>(
                             crane::any_cast<std::deque<crane::obj>>(a0)));
                       }))),
        std::deque<SigT<Prod<Nonterminal, std::deque<Symbol>>,
                        Prod<crane::obj, crane::obj>>>{}));

#endif // INCLUDED_ACTION_CONTAINER_CAST
