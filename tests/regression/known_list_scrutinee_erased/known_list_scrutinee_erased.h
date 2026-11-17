#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct List {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<typename List::template list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const typename List::template list<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<
                    typename List::template list<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a, l] =
                  std::get<typename List::template list<CraneU>::Cons>(
                      _other.v());
              return Cons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (l ? std::make_shared<typename List::template list<A>>(
                           crane_convert<typename List::template list<A>>(*l))
                     : nullptr)};
            }
          }()) {}

    static typename List::template list<A> nil() {
      return typename List::template list<A>(Nil{});
    }

    static typename List::template list<A>
    cons(A a, crane::shared_child_slot<typename List::template list<A>> l) {
      return typename List::template list<A>(Cons{std::move(a), l.take()});
    }

    // MANIPULATORS
    ~list() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      auto _next =
          [&](variant_t &_v) -> std::shared_ptr<typename List::template list<A>> {
            if (auto *_alt = std::get_if<Cons>(&_v)) {
              if (_alt->l && _alt->l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                return std::move(_alt->l);
              }
            }
            return nullptr;
          };
      std::shared_ptr<typename List::template list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1>
  static std::optional<T1> nth_error(const List::list<T1> &l, uint64_t n);
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Matching a literal [None] with a nested pattern: the known outer cons is
/// simplified away and the tail is matched as List<uint64_t>::nil() while the
/// alternative test names List<std::optional<crane::obj>>::Nil: the element
/// type of the literal was lost, and std::holds_alternative does not compile.
struct KnownListScrutineeErased {
  static inline const std::optional<uint64_t> t =
      List::template nth_error<uint64_t>(
          []() {
            List::list<std::optional<uint64_t>> l =
                List::template list<std::optional<uint64_t>>::nil();
            if (std::holds_alternative<
                    typename List::list<std::optional<uint64_t>>::Nil>(
                    l.v_mut())) {
              return List::template list<uint64_t>::cons(
                  UINT64_C(5), List::template list<uint64_t>::nil());
            } else {
              return List::template list<uint64_t>::cons(
                  UINT64_C(0), List::template list<uint64_t>::nil());
            }
          }(),
          UINT64_C(0));
};

template <typename T1>
std::optional<T1> List::nth_error(const List::list<T1> &l, uint64_t n) {
  if (n <= 0) {
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, _] = std::get<typename List::list<T1>::Cons>(l.v());
      return std::make_optional<T1>(a0);
    }
  } else {
    uint64_t n0 = n - 1;
    if (std::holds_alternative<typename List::list<T1>::Nil>(l.v())) {
      return std::optional<T1>();
    } else {
      const auto &[_, a10] = std::get<typename List::list<T1>::Cons>(l.v());
      return List::template nth_error<T1>(*a10, n0);
    }
  }
}
