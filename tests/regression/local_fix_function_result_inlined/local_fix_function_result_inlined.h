#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
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
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A local fixpoint returning a function, called with literal arguments so
/// the call is inlined (the beta-redex form in local_fix_returns_function is
/// fixed).
/// - t: under an applied observer, "no matching function for call to object
/// of type 'const (lambda ...)'": the closure for the partial application
/// passed go's written arguments last first.
/// - u: a branch returning a lambda next to one returning the accumulator:
/// "return type '(lambda ...)' must match previous return type
/// 'crane::fn<bool (uint64_t)>'": the let the inlined body became, in
/// expression position, was an IIFE with no declared return type.
struct LocalFixFunctionResultInlined {
  static inline const uint64_t t = []() {
    return []() {
      crane::fn<bool(List<uint64_t>)> w;
      auto go =
          [](List<uint64_t> l, crane::fn<bool(List<uint64_t>)>,
             List<uint64_t>)
               -> bool {
            // Loop replaces the tail recursion: each recursive call updates the
            // loop variables.
            List<uint64_t> _loop_l = std::move(l);
            while (true) {
              if (std::holds_alternative<typename List<uint64_t>::Nil>(
                      _loop_l.v_mut())) {
                return true;
              } else {
                auto &[_, a1] =
                    std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
                _loop_l = List<uint64_t>(*a1);
              }
            }
          };
      w = [=](List<uint64_t> _pa0) {
        return go(List<uint64_t>::nil(),
                  [](const List<uint64_t> &) { return false; }, _pa0);
      };
      if (w(List<uint64_t>::nil())) {
        return UINT64_C(1);
      } else {
        return UINT64_C(2);
      }
    }();
  }();
  static inline const bool u =
      (std::make_pair(
           []() -> crane::fn<bool(uint64_t)> {
             List<uint64_t> l = List<uint64_t>::nil();
             crane::fn<bool(uint64_t)> acc = [](uint64_t) { return false; };
             if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
               return acc;
             } else {
               return [](uint64_t) { return true; };
             }
           }(),
           true))
          .first(UINT64_C(0));
};
