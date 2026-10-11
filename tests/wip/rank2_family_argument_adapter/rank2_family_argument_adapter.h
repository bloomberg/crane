#ifndef INCLUDED_RANK2_FAMILY_ARGUMENT_ADAPTER
#define INCLUDED_RANK2_FAMILY_ARGUMENT_ADAPTER

#include "crane_fn.h"
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

struct Rank2FamilyArgumentAdapter {
  template <typename T1, typename T2, typename F1>
  static T1 grect2(const T1 &f, F1 &&f0, const List<T2> &l) {
    if (std::holds_alternative<typename List<T2>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List<T2>::Cons>(l.v());
      return crane_any_cast<T1>(
          f0(a0, *a1, grect2<T1, T2>(f, crane_erase_fn<T1>(f0), *a1)));
    }
  }

  template <typename T1> static uint64_t len2(const List<T1> &l) {
    static const auto erased_fn = crane::immortal(crane_erase_fn<crane::obj>(
        [](crane::obj, List<crane::obj>, uint64_t k) { return (k + 1); }));
    return grect2<uint64_t, T1>([]() { return UINT64_C(0); }(), erased_fn, l);
  }

  static inline const uint64_t result = len2<uint64_t>(List<uint64_t>::cons(
      UINT64_C(1), List<uint64_t>::cons(
                       UINT64_C(2), List<uint64_t>::cons(
                                        UINT64_C(3), List<uint64_t>::nil()))));
};

#endif // INCLUDED_RANK2_FAMILY_ARGUMENT_ADAPTER
