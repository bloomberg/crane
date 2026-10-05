#ifndef INCLUDED_LET_FIX
#define INCLUDED_LET_FIX

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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

struct LetFix {
  static uint64_t local_sum(const List<uint64_t> &l);

  template <typename T1> static List<T1> local_rev(const List<T1> &l) {
    {
      List<T1> _lc1_acc = List<T1>::nil();
      const List<T1> &_lc1_xs = l;
      const List<T1> *_lc1_loop_xs = &_lc1_xs;
      List<T1> _lc1_loop_acc = std::move(_lc1_acc);
      while (true) {
        if (std::holds_alternative<typename List<T1>::Nil>(_lc1_loop_xs->v())) {
          return _lc1_loop_acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename List<T1>::Cons>(_lc1_loop_xs->v());
          _lc1_loop_xs = crane_raw(a1);
          _lc1_loop_acc = List<T1>::cons(a0, std::move(_lc1_loop_acc));
        }
      }
    }
  }

  static List<uint64_t> local_flatten(const List<List<uint64_t>> &xss);
  static bool local_mem(uint64_t n, const List<uint64_t> &l);

  template <typename T1> static uint64_t local_length(const List<T1> &xs) {
    if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(xs.v());
      return (local_length<T1>(*a1) + 1);
    }
  }

  static constexpr uint64_t test_sum = UINT64_C(15);
  static inline const List<uint64_t> test_rev =
      local_rev<uint64_t>(List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
  static inline const List<uint64_t> test_flatten =
      local_flatten(List<List<uint64_t>>::cons(
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
  static constexpr bool test_mem_found = true;
  static constexpr bool test_mem_missing = false;
  static constexpr uint64_t test_length = UINT64_C(4);
};

#endif // INCLUDED_LET_FIX
