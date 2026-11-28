#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Datatypes {
  static crane::obj id(crane::obj x);
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

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct FitClosureAutoResult {
  struct pt {
    uint64_t px;
    bool py;
  };

  template <typename T1> static T1 pick(bool b, T1 x, T1 y) {
    if (b) {
      return x;
    } else {
      return y;
    }
  }

  template <typename T1> static T1 hd_or(T1 d, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return d;
    } else {
      const auto &[a0, _] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  template <typename T1> static T1 nth_or(const List<T1> &l, uint64_t n, T1 d) {
    return ListDef::template nth<T1>(n, l, std::move(d));
  }

  static inline const uint64_t via_hd_or =
      crane::any_cast<uint64_t>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
              Datatypes::id(crane_erase_fn(hd_or<crane::fn<uint64_t(uint64_t)>>(
                  [](uint64_t) { return UINT64_C(3); },
                  List<crane::fn<uint64_t(uint64_t)>>::nil()))))(
              crane::obj(UINT64_C(0))));
  static inline const uint64_t via_twice =
      crane::any_cast<uint64_t>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
              Datatypes::id(crane_erase_fn(twice<crane::fn<uint64_t(uint64_t)>>(
                  [](crane::fn<uint64_t(uint64_t)>) {
                    return [](uint64_t) { return UINT64_C(4); };
                  },
                  [](uint64_t) { return UINT64_C(0); }))))(
              crane::obj(UINT64_C(0))));
  static inline const uint64_t via_nth_or =
      crane::any_cast<pt>(crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
          Datatypes::id(crane_erase_fn(nth_or<crane::fn<pt(uint64_t)>>(
              List<crane::fn<pt(uint64_t)>>::nil(), UINT64_C(0),
              [](uint64_t) { return pt{UINT64_C(5), true}; }))))(
          crane::obj(UINT64_C(0))))
          .px;
  static inline const bool via_pick =
      crane::any_cast<bool>(crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
          Datatypes::id(crane_erase_fn(pick<crane::fn<bool(uint64_t)>>(
              true,
              [](uint64_t) { return true; },
              [](uint64_t) { return false; }))))(crane::obj(UINT64_C(0))));
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, _] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[_, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, std::move(default0));
    }
  }
}
