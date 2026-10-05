#ifndef INCLUDED_DOUBLE_TYPENAME
#define INCLUDED_DOUBLE_TYPENAME

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

template <typename M>
concept OrderedType = requires { typename M::t; };

struct DoubleTypename {
  template <OrderedType X> struct MakeMap {
    template <typename A> struct entry {
      // DATA
      typename X::t a0;
      A a1;

      // ACCESSORS
      entry<A> clone() const { return {a0, a1}; }

      template <typename CraneU>
        requires crane_convertible<CraneU, const A &>
      operator entry<CraneU>() const {
        return {a0, crane_convert<CraneU>(a1)};
      }

      // CREATORS
      static entry<A> entry0(typename X::t a0, A a1) {
        return {std::move(a0), std::move(a1)};
      }
    };

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, const typename X::t &,
                                     const T1 &>
    static T2 entry_rect(F0 &&f, const entry<T1> &e) {
      const auto &[a0, a1] = e;
      return f(a0, a1);
    }

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<T2, F0 &, const typename X::t &,
                                     const T1 &>
    static T2 entry_rec(F0 &&f, const entry<T1> &e) {
      const auto &[a0, a1] = e;
      return f(a0, a1);
    }

    template <typename T1>
    static List<typename X::t> keys(const List<entry<T1>> &l) {
      if (std::holds_alternative<typename List<entry<T1>>::Nil>(l.v())) {
        return List<typename X::t>::nil();
      } else {
        const auto &[a0, a1] = std::get<typename List<entry<T1>>::Cons>(l.v());
        const auto &[a00, a10] = a0;
        return List<typename X::t>::cons(a00, List<typename X::t>::nil());
      }
    }
  };

  struct NatOrd {
    using t = uint64_t;
  };

  using NatMap = MakeMap<NatOrd>;
  static inline const List<uint64_t> test =
      NatMap::template keys<uint64_t>(List<NatMap::entry<uint64_t>>::cons(
          NatMap::template entry<uint64_t>::entry0(UINT64_C(1), UINT64_C(2)),
          List<NatMap::entry<uint64_t>>::nil()));
};

#endif // INCLUDED_DOUBLE_TYPENAME
