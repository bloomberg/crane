#pragma once

#include "crane_fn.h"
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
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

/// A local fixpoint with a type binder of its own, let fix go {B}, inside
/// a definition polymorphic in A: Local_types.settle mints go's open
/// variables from 1, so B is numbered T1, the number of A, and
/// lowering reads it as A.  f's go takes const List<T1> &l and is
/// passed a List<pt>, which does not convert to List<uint64_t>.
///
/// Minting past the definition's variables (outer + 1) lifts go over
/// T1 and its own T2 and fixes f, but breaks h: the type of go's
/// x : B is a metavariable nothing in the body solves (the declared type
/// binds C of its own, so extraction does not unify it), minted as a
/// third variable rather than B; numbered from 1 it lands on B by
/// coincidence.  The binder needs its declared type first.
///
/// Extraction now unifies a let-bound fixpoint with its declared type also
/// where that type binds types of its own in front, each occurrence of one
/// left to inference, so x is B; the group's own variables are minted
/// past the definition's variables its signature names (from 1 where it
/// names none, as its body numbers a binder shadowing one by name); and the
/// helper it is lifted to is a template over
/// every variable up to its greatest, h's T1 included, since type
/// conversion reads a variable by its position.
struct LocalFixOwnTypeVariable {
  struct pt {
    uint64_t px;
    bool py;
  };

  template <typename T1, typename T2>
  static uint64_t f_crane_go(const List<T2> l, const List<T1> acc, const T1 a) {
    if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
      return acc.length();
    } else {
      const auto &[_, a1] = std::get<typename List<T2>::Cons>(l.v());
      return f_crane_go<T1, T2>(*a1, List<T1>::cons(a, acc), a);
    }
  }

  template <typename T1> static uint64_t f(T1 a) {
    return f_crane_go(
        List<pt>::cons(pt{UINT64_C(1), true},
                       List<pt>::cons(pt{UINT64_C(2), false}, List<pt>::nil())),
        List<T1>::cons(a, List<T1>::nil()), a);
  }

  static inline const uint64_t t = f<uint64_t>(UINT64_C(7));

  template <typename T1, typename T2, typename T3>
  static uint64_t h_crane_go(const List<T3> l, const T2 x) {
    if (std::holds_alternative<typename List<T3>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[_, a1] = std::get<typename List<T3>::Cons>(l.v());
      return (h_crane_go<T1, T2, T3>(*a1, x) + 1);
    }
  }

  template <typename T1, typename T2>
  static uint64_t h(const T1 &a, const T2 &b) {
    return ((h_crane_go<T1>(
                 List<T1>::cons(a, List<T1>::cons(a, List<T1>::nil())), b) +
             h_crane_go<T1>(List<T2>::cons(b, List<T2>::nil()), b)) +
            h_crane_go<T1>(List<bool>::cons(true, List<bool>::nil()), b));
  }

  static inline const uint64_t v = h<uint64_t, bool>(UINT64_C(1), false);
};
