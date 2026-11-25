#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

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

/// sumk is tail recursive and is loopified into a for, so it should run in
/// constant stack.  It did not: the continuation parameter k was a
/// std::function taken by value and then *copied* into the next
/// continuation's capture, rather than moved out of the dying parameter.  Each
/// iteration therefore copied the whole chain, and copying a chain of a
/// hundred thousand nested std::functions recursed a hundred thousand deep
/// and overflowed the stack.
///
/// Diagnosis (2026-11-24): that defect is gone.  A continuation is a shared,
/// immutable crane::fn, so the copy is a reference-count increment, and
/// sumk loopifies (the test was missing Set Crane Loopify, which it
/// needs to be about the loop at all; List.seq then builds its list in a
/// loop too).  Destroying the chain is iterative as well.  What still
/// overflows, at the suite's -O0, is calling the chain: _loop_k(0)
/// runs a hundred thousand closures, each tail-calling the next
/// (fun s => k (x + s)).  OCaml eliminates those tail calls; C++ does not
/// promise to, and at -O0 each level costs some 200 bytes of stack
/// through crane::fn's invocation thunk, so about 40000 levels exhaust
/// the default 8 MB stack.  The same program passes at -O1 and -O2,
/// and at -O0 with a 64 MB stack.  Guaranteed tail calls through closure
/// values would need a different calling convention for crane::fn (a
/// trampoline, or [clang::musttail], which needs matching signatures
/// the thunk does not have): a design question, not this defect.  Kept in
/// wip until it is decided.
struct CpsContinuationCopy {
  static uint64_t sumk(const List<uint64_t> &l,
                       const crane::fn<uint64_t(uint64_t)> &k) {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    crane::fn<uint64_t(uint64_t)> _loop_k = k;
    const List<uint64_t> *_loop_l = &l;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_l->v())) {
        return _loop_k(UINT64_C(0));
      } else {
        const auto &[a0, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_l->v());
        const List<uint64_t> &a1_value = *a1;
        _loop_k = [=](uint64_t s) { return _loop_k((a0 + s)); };
        _loop_l = &a1_value;
      }
    }
  }

  static inline const uint64_t run =
      sumk(ListDef::seq(UINT64_C(0), UINT64_C(100000)),
           [](uint64_t x) { return x; });
};
