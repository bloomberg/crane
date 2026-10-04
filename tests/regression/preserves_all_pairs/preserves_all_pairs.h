#ifndef INCLUDED_PRESERVES_ALL_PAIRS
#define INCLUDED_PRESERVES_ALL_PAIRS

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

struct ListDef {
  template <typename T1>
  static T1 nth(uint64_t n, const List<T1> &l, T1 default0);
};

struct PreservesAllPairs {
  struct state {
    List<uint64_t> regs;
    uint64_t acc;
  };

  static uint64_t get_reg(const state &s, uint64_t r);
  static uint64_t nibble_of_nat(uint64_t n);
  static uint64_t get_reg_pair(const state &s, uint64_t r);
  static state execute_add(const state &s, uint64_t r);
  static state execute_ld(const state &s, uint64_t r);
  static state execute_sub(const state &s, uint64_t r);
  static inline const state sample =
      state{List<uint64_t>::cons(
                UINT64_C(2),
                List<uint64_t>::cons(
                    UINT64_C(9),
                    List<uint64_t>::cons(
                        UINT64_C(4),
                        List<uint64_t>::cons(
                            UINT64_C(7),
                            List<uint64_t>::cons(
                                UINT64_C(8),
                                List<uint64_t>::cons(
                                    UINT64_C(1), List<uint64_t>::nil())))))),
            UINT64_C(13)};
  static inline const bool add_preserves_pairs =
      get_reg_pair(execute_add(sample, UINT64_C(4)), UINT64_C(2)) ==
      get_reg_pair(sample, UINT64_C(2));
  static inline const bool ld_preserves_pairs =
      get_reg_pair(execute_ld(sample, UINT64_C(4)), UINT64_C(2)) ==
      get_reg_pair(sample, UINT64_C(2));
  static inline const bool sub_preserves_pairs =
      get_reg_pair(execute_sub(sample, UINT64_C(4)), UINT64_C(2)) ==
      get_reg_pair(sample, UINT64_C(2));
  static inline const bool t =
      ((add_preserves_pairs && ld_preserves_pairs) && sub_preserves_pairs);
};

template <typename T1>
T1 ListDef::nth(uint64_t n, const List<T1> &l, T1 default0) {
  if (n <= 0) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  } else {
    uint64_t m = n - 1;
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l.v());
      return ListDef::template nth<T1>(m, *a10, std::move(default0));
    }
  }
}

#endif // INCLUDED_PRESERVES_ALL_PAIRS
