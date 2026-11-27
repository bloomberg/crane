#pragma once

#include "crane_fn.h"
#include "crane_variant.h"
#include "obj.h"
#include "shared_block.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <utility>

template <typename A> struct List;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    crane::shared_box<List<A>> l;
  };

  using variant_t = crane::shared_variant<Nil, Cons>;

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
          if (crane::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                crane::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? crane::shared_box<List<A>>::make(
                         crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))});
  }

  static List<A> cons_crane_reuse(List<A> _tok, A a, List<A> l) {
    auto _alt =
        Cons{std::move(a), crane::shared_box<List<A>>::make(std::move(l))};
    if (_tok.v_.try_reuse(std::move(_alt))) {
      return _tok;
    }
    return List<A>(Cons{std::move(_alt)});
  }

  // MANIPULATORS
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
      if (crane::holds_alternative<_call>(_popped)) {
        auto _f = std::move(crane::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (crane::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = crane::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(crane::get<_after_length_in_Cons>(_popped));
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
/// Under Reuse and SharedVariant, a polymorphic non-tail local fixpoint
/// building a list of lists fails the ownership check under CRANE_CHECK_IR=1:
/// "frame save: a let a frame machine resumes at is generated saving its
/// frame otherwise than it was before".  The match's reuse arm generates
/// the branch, and the let in it, again under the arm's plan, which owns
/// what the shared arm borrows; the save at that let now records what both
/// move.
struct ReuseSharedPolyFrameSave {
  template <typename T1> static List<List<T1>> f(const T1 &) {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto k = crane::immortal(
        List<List<T1>>::cons(List<T1>::nil(), List<List<T1>>::nil()));
    auto go_impl =
        [](auto &_self_go, List<List<T1>> l, List<List<T1>> acc) -> List<
            List<T1>> {
          // Reuse the matched cell in place when this is its only owner;
          // otherwise rebuild.
          if (l.v().index() == 1) {
            if (l.v().unique()) {
              List<T1> e = std::move(
                  crane::get<typename List<List<T1>>::Cons>(l.v_mut()).a);
              List<List<T1>> rest = std::move(
                  *crane::get<typename List<List<T1>>::Cons>(l.v_mut()).l);
              List<List<T1>> rv =
                  _self_go(_self_go, std::move(rest), std::move(acc));
              return List<List<T1>>::cons_crane_reuse(
                  std::move(l), std::move(e), std::move(rv));
            } else {
              if (crane::holds_alternative<typename List<List<T1>>::Nil>(l.v())) {
                return acc;
              } else {
                const auto &[a0, a1] =
                    crane::get<typename List<List<T1>>::Cons>(l.v());
                List<List<T1>> rv = _self_go(_self_go, *a1, std::move(acc));
                return List<List<T1>>::cons(a0, std::move(rv));
              }
            }
          } else {
            if (crane::holds_alternative<typename List<List<T1>>::Nil>(l.v())) {
              return acc;
            } else {
              const auto &[a0, a1] =
                  crane::get<typename List<List<T1>>::Cons>(l.v());
              List<List<T1>> rv = _self_go(_self_go, *a1, std::move(acc));
              return List<List<T1>>::cons(a0, std::move(rv));
            }
          }
        };
    List<List<T1>> _lc1_l = k;
    List<List<T1>> _lc1_acc = k;
    return go_impl(go_impl, std::move(_lc1_l), std::move(_lc1_acc));
  }

  static inline const uint64_t t = f<uint64_t>(UINT64_C(1)).length();
};
