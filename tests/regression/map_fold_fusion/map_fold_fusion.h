#ifndef INCLUDED_MAP_FOLD_FUSION
#define INCLUDED_MAP_FOLD_FUSION

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

/// A right fold of a map, fused into one traversal where both callbacks are
/// pure under declared meanings and the mapped list is used once.
struct MapFoldFusion {
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<list<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    list() {}

    explicit list(Nil _v) : v_(_v) {}

    explicit list(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    list(const list<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<list<A>>(nullptr),
              [](const list<CraneU> &_cell) -> const list<CraneU> * {
                if (std::holds_alternative<typename list<CraneU>::Cons>(
                        _cell.v())) {
                  return std::get<typename list<CraneU>::Cons>(_cell.v())
                      .l.get();
                } else {
                  return nullptr;
                }
              },
              [&](const list<CraneU> &_other,
                  std::shared_ptr<list<A>> _below) -> variant_t {
                if (std::holds_alternative<typename list<CraneU>::Nil>(
                        _other.v())) {
                  return Nil{};
                } else {
                  const auto &[a, l] =
                      std::get<typename list<CraneU>::Cons>(_other.v());
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
                return std::make_shared<list<A>>(std::move(_alt));
              })) {}

    static list<A> nil() { return list<A>(Nil{}); }

    static list<A> cons(A a, list<A> l) {
      return list<A>(
          Cons{std::move(a), std::make_shared<list<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<list<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    list(const list &) = default;
    list &operator=(const list &) = default;
    list(list &&) = default;
    list &operator=(list &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 list_rect(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 list_rec(T2 f, F1 &&f0, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f0(a0, *a1, list_rec<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static list<T2> map(F0 &&f, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return list<T2>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return list<T2>::cons(f(a0), map<T1, T2>(f, *a1));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &, T2>
  static T2 foldr(F0 &&f, T2 z, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return z;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return f(a0, foldr<T1, T2>(f, std::move(z), *a1));
    }
  }

  template <typename T1> static uint64_t length(const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return (length<T1>(*a1) + 1);
    }
  }

  /// Fused: a declared operation, partly applied, and a declared operation.
  static uint64_t sum_succ(const list<uint64_t> &l);
  /// Fused: lambdas, and a reducer that is not associative -- the fold's
  /// association is kept.
  static uint64_t alt_double(const list<uint64_t> &l);
  /// Fused across element types: the fold walks the map's input.
  static uint64_t count_big(const list<uint64_t> &l);
  /// Declined: twice has no declared meaning.
  static uint64_t twice(uint64_t x);
  static uint64_t sum_twice(const list<uint64_t> &l);
  /// Declined: the mapped list is used twice.
  static uint64_t sum_and_length(const list<uint64_t> &l);
};

#endif // INCLUDED_MAP_FOLD_FUSION
