#ifndef INCLUDED_NO_OPTIMIZE_FOLD_LEFT_ACCUMULATOR
#define INCLUDED_NO_OPTIMIZE_FOLD_LEFT_ACCUMULATOR

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, const A &>
  T1 fold_left(F0 &&f, const A &x1_) const {
    auto fold_left0_impl = [&](auto &_self_fold_left0, const List<A> &l,
                               T1 a0) -> T1 {
      if (std::holds_alternative<typename List<A>::Nil>(l.v())) {
        return a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(l.v());
        return _self_fold_left0(_self_fold_left0, *a2, f(a0, a1));
      }
    };
    {
      const List<A> &_lc1_l = *this;
      T1 _lc1_a0 = x1_;
      return fold_left0_impl(fold_left0_impl, _lc1_l, std::move(_lc1_a0));
    }
  }

  uint64_t length() const {
    auto length0_impl = [](auto &_self_length0, const List<A> &l) -> uint64_t {
      if (std::holds_alternative<typename List<A>::Nil>(l.v())) {
        return UINT64_C(0);
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(l.v());
        return (_self_length0(_self_length0, *a1) + 1);
      }
    };
    {
      const List<A> &_lc1_l = *this;
      return length0_impl(length0_impl, _lc1_l);
    }
  }
};

struct NoOptimizeFoldLeftAccumulator {
  static List<uint64_t> rev_(const List<uint64_t> &l);
  static inline const uint64_t result =
      rev_(List<uint64_t>::cons(
               UINT64_C(1),
               List<uint64_t>::cons(
                   UINT64_C(2),
                   List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))))
          .length();
};

#endif // INCLUDED_NO_OPTIMIZE_FOLD_LEFT_ACCUMULATOR
