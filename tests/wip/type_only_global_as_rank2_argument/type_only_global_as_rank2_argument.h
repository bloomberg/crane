#ifndef INCLUDED_TYPE_ONLY_GLOBAL_AS_RANK2_ARGUMENT
#define INCLUDED_TYPE_ONLY_GLOBAL_AS_RANK2_ARGUMENT

#include "crane_fn.h"
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

struct TypeOnlyGlobalAsRank2Argument {
  template <typename T1, typename T2, typename F1>
  static T1 grect(const T1 &f, F1 &&f0, const List<T2> &l) {
    if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
      return crane_any_cast<T1>(
          f0(a0, *a1, grect<T1, T2>(f, crane_erase_fn<T1>(f0), *a1)));
    }
  }

  template <typename T1>
  static uint64_t step(const T1 &, const List<T1> &, uint64_t k) {
    return (k + 1);
  }

  static constexpr uint64_t base = UINT64_C(0);

  template <typename T1> static uint64_t len(const List<T1> &l) {
    return grect<uint64_t, T1>(
        []() -> uint64_t { return base(); },
        [](const auto &a0, const auto &a1, const uint64_t &a2) -> uint64_t {
          return step<crane::obj>(crane_convert<crane::obj>(a0),
                                  crane_convert<List<crane::obj>>(a1),
                                  std::forward<decltype(a2)>(a2));
        },
        l);
  }

  static inline const uint64_t result = len<bool>(
      List<bool>::cons(true, List<bool>::cons(true, List<bool>::nil())));
};

#endif // INCLUDED_TYPE_ONLY_GLOBAL_AS_RANK2_ARGUMENT
