#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
enum class Comparison;

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

enum class Comparison { EQ, LT, GT };
template <typename M>
concept Cmp = requires {
  typename M::t;
  {
    M::compare(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Comparison>;
};

struct PairAbstractComponentsByReference {
  template <Cmp A, Cmp B> struct PairCmp {
    using t = std::pair<typename A::t, typename B::t>;

    static Comparison
    compare(const std::pair<typename A::t, typename B::t> &x,
            const std::pair<typename A::t, typename B::t> &y) {
      const auto &[a, b] = x;
      const auto &[a_, b_] = y;
      switch (A::compare(a, a_)) {
      case Comparison::EQ: {
        return B::compare(b, b_);
      }
      case Comparison::LT: {
        return Comparison::LT;
      }
      case Comparison::GT: {
        return Comparison::GT;
      }
      default:
        std::unreachable();
      }
    }

    static bool eqb(const std::pair<typename A::t, typename B::t> &x,
                    const std::pair<typename A::t, typename B::t> &y) {
      switch (compare(x, y)) {
      case Comparison::EQ: {
        return true;
      }
      default: {
        return false;
      }
      }
    }
  };

  template <Cmp A> struct OptCmp {
    using t = std::optional<typename A::t>;

    static Comparison compare(const std::optional<typename A::t> &x,
                              const std::optional<typename A::t> &y) {
      if (x.has_value()) {
        const typename A::t &a = *x;
        if (y.has_value()) {
          const typename A::t &a_ = *y;
          return A::compare(a, a_);
        } else {
          return Comparison::GT;
        }
      } else {
        if (y.has_value()) {
          const typename A::t &_x = *y;
          return Comparison::LT;
        } else {
          return Comparison::EQ;
        }
      }
    }
  };

  struct NatListCmp {
    using t = List<uint64_t>;
    static Comparison compare(const List<uint64_t> &x, const List<uint64_t> &y);
  };

  struct NatCmp {
    using t = uint64_t;
    static Comparison compare(uint64_t x0_, uint64_t x1_);
  };

  using P = PairCmp<NatListCmp, NatCmp>;
  using O = OptCmp<NatListCmp>;
  static uint64_t sum_pair(std::pair<uint64_t, uint64_t> p);
  static inline const Comparison test_pair =
      P::compare(std::make_pair(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
                                UINT64_C(3)),
                 std::make_pair(List<uint64_t>::cons(
                     UINT64_C(1),
                     List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
                                UINT64_C(4)));
  static inline const Comparison test_opt = O::compare(
      std::make_optional<List<uint64_t>>(
          List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil())),
      std::make_optional<List<uint64_t>>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil()))));
};
