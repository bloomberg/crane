#ifndef INCLUDED_CLOSURE_COPY_SHARES
#define INCLUDED_CLOSURE_COPY_SHARES

#include "crane_fn.h"
#include "fn.h"
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
};

/// A closure is a shared, immutable value: copying one copies a pointer.
/// The closures below capture a list and other closures, so a copy that
/// cloned its captures would allocate.
struct ClosureCopyShares {
  static uint64_t sum(const List<uint64_t> &l);
  /// Captures a list.
  static uint64_t adder(const List<uint64_t> &l, uint64_t x);

  /// Captures two closures.
  template <typename F0, typename F1>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t> &&
             std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static uint64_t compose(F0 &&f, F1 &&g, uint64_t x) {
    return f(g(x));
  }

  /// Stored in a list, so they are function values rather than functions.
  static inline const List<crane::fn<uint64_t(uint64_t)>> closures = []() {
    return []() {
      crane::fn<uint64_t(uint64_t)> a = [](uint64_t _x0) -> uint64_t {
        return adder(
            List<uint64_t>::cons(
                UINT64_C(1),
                List<uint64_t>::cons(
                    UINT64_C(2),
                    List<uint64_t>::cons(
                        UINT64_C(3),
                        List<uint64_t>::cons(
                            UINT64_C(4),
                            List<uint64_t>::cons(
                                UINT64_C(5),
                                List<uint64_t>::cons(
                                    UINT64_C(6),
                                    List<uint64_t>::cons(
                                        UINT64_C(7),
                                        List<uint64_t>::cons(
                                            UINT64_C(8),
                                            List<uint64_t>::nil())))))))),
            _x0);
      };
      return List<crane::fn<uint64_t(uint64_t)>>::cons(
          a, List<crane::fn<uint64_t(uint64_t)>>::cons(
                 [=](uint64_t _x0) -> uint64_t {
                   return compose(
                       a,
                       [=](uint64_t _x0) -> uint64_t {
                         return compose([](uint64_t x) { return (x + 1); }, a,
                                        _x0);
                       },
                       _x0);
                 },
                 List<crane::fn<uint64_t(uint64_t)>>::nil()));
    }();
  }();
};

#endif // INCLUDED_CLOSURE_COPY_SHARES
