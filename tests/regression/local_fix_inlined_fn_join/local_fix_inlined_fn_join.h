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

struct LocalFixInlinedFnJoin {
  static inline const uint64_t result = []() {
    return []() {
      crane::fn<uint64_t(uint64_t)> w;
      List<bool> l = List<bool>::nil();
      crane::fn<uint64_t(uint64_t)> acc = [](uint64_t) { return UINT64_C(1); };
      w = [&]() -> crane::fn<uint64_t(uint64_t)> {
        if (std::holds_alternative<typename List<bool>::Nil>(l.v_mut())) {
          return std::move(acc);
        } else {
          auto &[_, a1] = std::get<typename List<bool>::Cons>(l.v_mut());
          const List<bool> &a1_value = *a1;
          auto go2 =
              [](List<bool> l2, crane::fn<uint64_t(uint64_t)>,
                 uint64_t)
                   -> uint64_t {
                // Loop replaces the tail recursion: each recursive call updates
                // the loop variables.
                List<bool> _loop_l2 = std::move(l2);
                while (true) {
                  if (std::holds_alternative<typename List<bool>::Nil>(
                          _loop_l2.v_mut())) {
                    return UINT64_C(0);
                  } else {
                    auto &[_, a10] =
                        std::get<typename List<bool>::Cons>(_loop_l2.v_mut());
                    _loop_l2 = List<bool>(*a10);
                  }
                }
              };
          return [=, a1_value = a1_value](uint64_t _pa0) {
            return go2(a1_value, [](uint64_t) { return UINT64_C(0); }, _pa0);
          };
        }
      }();
      return w(UINT64_C(0)) + w(UINT64_C(1));
    }();
  }();
};
