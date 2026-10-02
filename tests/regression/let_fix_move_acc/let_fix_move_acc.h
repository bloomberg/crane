#ifndef INCLUDED_LET_FIX_MOVE_ACC
#define INCLUDED_LET_FIX_MOVE_ACC

#include "crane_fn.h"
#include "obj.h"
#include <any>
#include <atomic>
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct LetFixMoveAcc {
  template <typename T1> static List<T1> reverse_list(const List<T1> &l) {
    auto go_impl = [](auto &_self_go, const List<T1> &xs,
                      List<T1> acc) -> List<T1> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(xs.v());
        return _self_go(_self_go, *a1, List<T1>::cons(a0, std::move(acc)));
      }
    };
    auto go = [&](const List<T1> &xs, List<T1> acc) -> List<T1> {
      return go_impl(go_impl, xs, acc);
    };
    return go(l, List<T1>::nil());
  }

  template <typename T1> static List<T1> snoc(const List<T1> &l, const T1 &x) {
    auto rev_impl = [](auto &_self_rev, const List<T1> &xs,
                       List<T1> acc) -> List<T1> {
      if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(xs.v());
        return _self_rev(_self_rev, *a1, List<T1>::cons(a0, std::move(acc)));
      }
    };
    auto rev = [&](const List<T1> &xs, List<T1> acc) -> List<T1> {
      return rev_impl(rev_impl, xs, acc);
    };
    return rev(rev(l, List<T1>::nil()), List<T1>::cons(x, List<T1>::nil()));
  }

  static inline const List<uint64_t> test_rev =
      reverse_list<uint64_t>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));

  static inline const List<uint64_t> test_snoc = snoc<uint64_t>(
      List<uint64_t>::cons(
          UINT64_C(10),
          List<uint64_t>::cons(UINT64_C(20), List<uint64_t>::nil())),
      UINT64_C(30));
};

#endif // INCLUDED_LET_FIX_MOVE_ACC
