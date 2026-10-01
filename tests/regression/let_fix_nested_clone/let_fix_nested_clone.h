#ifndef INCLUDED_LET_FIX_NESTED_CLONE
#define INCLUDED_LET_FIX_NESTED_CLONE

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

struct LetFixNestedClone {
  static uint64_t sum_nested(const List<List<uint64_t>> &ll);
  static uint64_t count_nested(const List<List<uint64_t>> &ll);
  static inline const uint64_t test_sum = sum_nested(List<List<uint64_t>>::cons(
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
      List<List<uint64_t>>::cons(
          List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()),
          List<List<uint64_t>>::cons(
              List<uint64_t>::cons(
                  UINT64_C(4),
                  List<uint64_t>::cons(
                      UINT64_C(5), List<uint64_t>::cons(
                                       UINT64_C(6), List<uint64_t>::nil()))),
              List<List<uint64_t>>::nil()))));

  static inline const uint64_t test_count =
      count_nested(List<List<uint64_t>>::cons(
          List<uint64_t>::cons(
              UINT64_C(1),
              List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())),
          List<List<uint64_t>>::cons(
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()),
              List<List<uint64_t>>::cons(
                  List<uint64_t>::cons(
                      UINT64_C(4),
                      List<uint64_t>::cons(
                          UINT64_C(5),
                          List<uint64_t>::cons(UINT64_C(6),
                                               List<uint64_t>::nil()))),
                  List<List<uint64_t>>::nil()))));
};

#endif // INCLUDED_LET_FIX_NESTED_CLONE
