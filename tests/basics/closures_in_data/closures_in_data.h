#ifndef INCLUDED_CLOSURES_IN_DATA
#define INCLUDED_CLOSURES_IN_DATA

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
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
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct ClosuresInData {
  /// A list of functions: successor, doubling, and squaring.
  static inline const List<crane::fn<uint64_t(uint64_t)>> fn_list =
      List<crane::fn<uint64_t(uint64_t)>>::cons(
          [](uint64_t x) { return (x + 1); },
          List<crane::fn<uint64_t(uint64_t)>>::cons(
              [](uint64_t x) { return (x + x); },
              List<crane::fn<uint64_t(uint64_t)>>::cons(
                  [](uint64_t x) { return (x * x); },
                  List<crane::fn<uint64_t(uint64_t)>>::nil())));
  /// apply_all fns x applies every function in fns to x,
  /// returning the list of results.
  static List<uint64_t>
  apply_all(const List<crane::fn<uint64_t(uint64_t)>> &fns, uint64_t x);

  /// A pair of invertible transformations: forward and backward.
  struct transform {
    crane::fn<uint64_t(uint64_t)> forward;
    crane::fn<uint64_t(uint64_t)> backward;
  };

  /// A transform that doubles via addition and halves via division.
  static inline const transform double_transform =
      transform{[](uint64_t x) { return (x + x); },
                [](uint64_t x) { return (UINT64_C(2) ? x / UINT64_C(2) : 0); }};
  static uint64_t apply_forward(const transform &t, uint64_t x);
  static uint64_t apply_backward(const transform &t, uint64_t x);
  /// compose_all fns x folds fns left, threading x through each
  /// function in sequence.
  static uint64_t compose_all(const List<crane::fn<uint64_t(uint64_t)>> &fns,
                              uint64_t x);
  /// A pipeline of transformations: increment, double, then add 10.
  static inline const List<crane::fn<uint64_t(uint64_t)>> pipeline =
      List<crane::fn<uint64_t(uint64_t)>>::cons(
          [](uint64_t x) { return (x + UINT64_C(1)); },
          List<crane::fn<uint64_t(uint64_t)>>::cons(
              [](uint64_t x) { return (x * UINT64_C(2)); },
              List<crane::fn<uint64_t(uint64_t)>>::cons(
                  [](uint64_t x) { return (x + UINT64_C(10)); },
                  List<crane::fn<uint64_t(uint64_t)>>::nil())));
  /// maybe_apply mf x applies function mf to x if present,
  /// otherwise returns x unchanged.
  static uint64_t
  maybe_apply(const std::optional<crane::fn<uint64_t(uint64_t)>> &mf,
              uint64_t x);
  static inline const List<uint64_t> test_apply_all =
      apply_all(fn_list, UINT64_C(5));
  static inline const uint64_t test_forward =
      apply_forward(double_transform, UINT64_C(7));
  static inline const uint64_t test_backward =
      apply_backward(double_transform, UINT64_C(14));
  static inline const uint64_t test_compose =
      compose_all(pipeline, UINT64_C(3));
  static inline const uint64_t test_maybe_some =
      maybe_apply(std::make_optional<crane::fn<uint64_t(uint64_t)>>(
                      [](uint64_t x) { return (x + 1); }),
                  UINT64_C(41));
  static inline const uint64_t test_maybe_none =
      maybe_apply(std::optional<crane::fn<uint64_t(uint64_t)>>(), UINT64_C(42));
};

#endif // INCLUDED_CLOSURES_IN_DATA
