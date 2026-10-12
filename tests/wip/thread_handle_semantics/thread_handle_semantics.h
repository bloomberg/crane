#ifndef INCLUDED_THREAD_HANDLE_SEMANTICS
#define INCLUDED_THREAD_HANDLE_SEMANTICS

#include "crane_fn.h"
#include "obj.h"
#include "shared_block.h"
#include <atomic>
#include <chrono>
#include <crane_itree.h>
#include <cstdint>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <thread>
#include <utility>
#include <variant>
static_assert(crane::rc_is_atomic,
              "this unit spawns threads, but a header included before it chose "
              "CRANE_NON_ATOMIC_RC");

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

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
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

struct ThreadHandleSemantics {
  static void work(uint64_t _x);
  static uint64_t never_joined(uint64_t n);
  static uint64_t joined_twice(uint64_t n);
  static List<std::thread> spawn_all(const List<uint64_t> &l);
  static void join_all(const List<std::thread> &l);
  static inline const uint64_t r1 = never_joined(UINT64_C(3));
  static inline const uint64_t r2 = joined_twice(UINT64_C(4));
  static inline const uint64_t r3 = []() {
    List<std::thread> hs = spawn_all(List<uint64_t>::cons(
        UINT64_C(1),
        List<uint64_t>::cons(
            UINT64_C(2),
            List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
    join_all(hs);
    return UINT64_C(7);
  }();
};

#endif // INCLUDED_THREAD_HANDLE_SEMANTICS
