#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
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

struct NestedFixAliasResult {
  template <typename a> using st = crane::fn<std::pair<a, uint64_t>(uint64_t)>;

  template <typename T1> static st<T1> sret(T1 a) {
    return [=, a = std::move(a)](uint64_t s) { return std::make_pair(a, s); };
  }

  static inline const st<uint64_t> f1 =
      [](uint64_t eta0_) -> std::pair<uint64_t, uint64_t> {
        // Built on the first call and immortal: every thread reads it without
        // touching its counts.
        static const auto sret_1 = crane::immortal(sret<uint64_t>(UINT64_C(0)));
        List<bool> l = List<bool>::nil();
        st<uint64_t> acc = sret<uint64_t>(UINT64_C(4));
        if (std::holds_alternative<typename List<bool>::Nil>(l.v_mut())) {
          auto inner =
              [](const List<uint64_t> &m, st<uint64_t> acc2) -> st<uint64_t> {
                // Loop replaces the tail recursion: each recursive call updates
                // the loop variables.
                const List<uint64_t> *_loop_m = &m;
                while (true) {
                  if (std::holds_alternative<typename List<uint64_t>::Nil>(
                          _loop_m->v())) {
                    return acc2;
                  } else {
                    const auto &[_, a10] =
                        std::get<typename List<uint64_t>::Cons>(_loop_m->v());
                    _loop_m = crane_raw(a10);
                  }
                }
              };
          return inner(List<uint64_t>::nil(), std::move(acc), eta0_);
        } else {
          return sret_1(eta0_);
        }
      };
  static inline const uint64_t result = f1(UINT64_C(0)).first;
};
