#ifndef INCLUDED_HIGHER_ORDER
#define INCLUDED_HIGHER_ORDER

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct HigherOrder {
  /// A simple polymorphic list type.
  template <typename A> struct list {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      std::shared_ptr<list<A>> a1;
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
                      .a1.get();
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
                  const auto &[a0, a1] =
                      std::get<typename list<CraneU>::Cons>(_other.v());
                  return Cons{
                      [&]() -> A {
                        if constexpr (crane_convertible<A, const CraneU &>) {
                          return crane_convert<A>(a0);
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

    static list<A> cons(A a0, list<A> a1) {
      return list<A>(
          Cons{std::move(a0), std::make_shared<list<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~list() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<list<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a1);
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
  static T2 list_rec(const T2 &f, F1 &&f0, const list<T1> &l) {
    return list_rect<T1, T2>(f, f0, l);
  }

  /// map f l applies f to each element of l, producing a new list.
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

  /// foldr f z l folds l from the right using f with initial
  /// accumulator z.
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

  /// foldl f z l folds l from the left using f with initial
  /// accumulator z. This is tail-recursive.
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &&, const T1 &>
  static T2 foldl(F0 &&f, T2 z, const list<T1> &l) {
    if (std::holds_alternative<typename list<T1>::Nil>(l.v())) {
      return z;
    } else {
      const auto &[a0, a1] = std::get<typename list<T1>::Cons>(l.v());
      return foldl<T1, T2>(f, f(std::move(z), a0), *a1);
    }
  }

  /// compose g f returns the composition of g after f.
  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, T2> &&
             std::is_invocable_r_v<T2, F1 &, const T1 &>
  static T3 compose(F0 &&g, F1 &&f, const T1 &x) {
    return g(f(x));
  }

  /// iterate n f x applies f to x a total of n times.
  template <typename T1, typename F1>
  static T1 iterate(uint64_t n, F1 &&f, T1 x) {
    if (n <= 0) {
      return x;
    } else {
      uint64_t m = n - 1;
      return f(iterate<T1>(m, f, std::move(x)));
    }
  }

  /// adder n returns a function that adds n to its argument.
  static uint64_t adder(uint64_t x0_, uint64_t x1_);

  /// twice f returns a function that applies f two times.
  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  /// pipe x f applies f to x, simulating a pipeline operator.
  template <typename T1, typename T2, typename F1>
    requires std::is_invocable_r_v<T2, F1 &, const T1 &>
  static T2 pipe(const T1 &x, F1 &&f) {
    return f(x);
  }

  static inline const list<uint64_t> test_list = list<uint64_t>::cons(
      UINT64_C(1),
      list<uint64_t>::cons(
          UINT64_C(2),
          list<uint64_t>::cons(
              UINT64_C(3),
              list<uint64_t>::cons(
                  UINT64_C(4),
                  list<uint64_t>::cons(UINT64_C(5), list<uint64_t>::nil())))));
  static constexpr uint64_t test_map = UINT64_C(20);
  static constexpr uint64_t test_foldr = UINT64_C(15);
  static constexpr uint64_t test_foldl = UINT64_C(15);
  static constexpr uint64_t test_compose = UINT64_C(8);
  static constexpr uint64_t test_iterate = UINT64_C(6);
  static constexpr uint64_t test_adder = UINT64_C(8);
  static constexpr uint64_t test_twice = UINT64_C(7);
  static constexpr uint64_t test_pipe = UINT64_C(8);
};

#endif // INCLUDED_HIGHER_ORDER
