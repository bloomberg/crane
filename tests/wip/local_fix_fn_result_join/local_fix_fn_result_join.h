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

struct LocalFixFnResultJoin {
  static inline const uint64_t result = []() {
    return []() {
      crane::fn<uint64_t(uint64_t)> f;
      List<uint64_t> l = List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())));
      crane::fn<uint64_t(uint64_t)> acc = [](uint64_t) { return UINT64_C(3); };
      f = [&]() {
        if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
          return std::move(acc);
        } else {
          auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
          const List<uint64_t> &a1_value = *a1;
          List<std::pair<bool, uint64_t>> k = [&]() {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    a1_value.v())) {
              return List<std::pair<bool, uint64_t>>::nil();
            } else {
              const auto &[_, a10] =
                  std::get<typename List<uint64_t>::Cons>(a1_value.v());
              auto &&_sv = *a10;
              if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
                return List<std::pair<bool, uint64_t>>::cons(
                    std::make_pair(false, UINT64_C(12)),
                    List<std::pair<bool, uint64_t>>::nil());
              } else {
                return List<std::pair<bool, uint64_t>>::cons(
                    std::make_pair(false, UINT64_C(1)),
                    List<std::pair<bool, uint64_t>>::cons(
                        std::make_pair(true, UINT64_C(14)),
                        List<std::pair<bool, uint64_t>>::nil()));
              }
            }
          }();
          if (std::holds_alternative<
                  typename List<std::pair<bool, uint64_t>>::Nil>(k.v_mut())) {
            return [](uint64_t) { return UINT64_C(0); };
          } else {
            List<uint64_t> m = List<uint64_t>::cons(
                UINT64_C(3),
                List<uint64_t>::cons(UINT64_C(12), List<uint64_t>::nil()));
            if (std::holds_alternative<typename List<uint64_t>::Nil>(m.v_mut())) {
              return [](uint64_t) { return UINT64_C(10); };
            } else {
              return std::move(acc);
            }
          }
        }
      }();
      return (f(UINT64_C(1)) + f(UINT64_C(2)));
    }();
  }();
};
