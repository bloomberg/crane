#ifndef INCLUDED_CALLABLE_CONSTRAINT_CATEGORIES
#define INCLUDED_CALLABLE_CONSTRAINT_CATEGORIES

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct CallableConstraintCategories {
  /// A callable parameter's constraint states the calls the body makes, with
  /// the operands' real categories: map hands its callback a borrowed
  /// element, curry a temporary pair, foldl a moved accumulator.
  template <typename A> struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      A a;
      std::shared_ptr<lst<A>> l;
    };

    using variant_t = std::variant<Nil, Cons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    lst() {}

    explicit lst(Nil _v) : v_(_v) {}

    explicit lst(Cons _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    lst(const lst<CraneU> &_other)
        : v_(crane_convert_spine(
              _other, std::shared_ptr<lst<A>>(nullptr),
              [](const lst<CraneU> &_cell) -> const lst<CraneU> * {
                if (std::holds_alternative<typename lst<CraneU>::Cons>(
                        _cell.v())) {
                  return std::get<typename lst<CraneU>::Cons>(_cell.v())
                      .l.get();
                } else {
                  return nullptr;
                }
              },
              [&](const lst<CraneU> &_other,
                  std::shared_ptr<lst<A>> _below) -> variant_t {
                if (std::holds_alternative<typename lst<CraneU>::Nil>(
                        _other.v())) {
                  return Nil{};
                } else {
                  const auto &[a, l] =
                      std::get<typename lst<CraneU>::Cons>(_other.v());
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
                return std::make_shared<lst<A>>(std::move(_alt));
              })) {}

    static lst<A> nil() { return lst<A>(Nil{}); }

    static lst<A> cons(A a, lst<A> l) {
      return lst<A>(Cons{std::move(a), std::make_shared<lst<A>>(std::move(l))});
    }

    // MANIPULATORS
    ~lst() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<lst<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->l && _alt->l.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->l);
          }
        }
        return nullptr;
      };
      std::shared_ptr<lst<A>> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    lst(const lst &) = default;
    lst &operator=(const lst &) = default;
    lst(lst &&) = default;
    lst &operator=(lst &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T2 lst_rect(T2 f, F1 &&f0, const lst<T1> &l) {
    if (std::holds_alternative<typename lst<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, l1] = std::get<typename lst<T1>::Cons>(l.v());
      return f0(a0, *l1, lst_rect<T1, T2>(std::move(f), f0, *l1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 lst_rec(T2 f, F1 &&f0, const lst<T1> &l) {
    if (std::holds_alternative<typename lst<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, l1] = std::get<typename lst<T1>::Cons>(l.v());
      return f0(a0, *l1, lst_rec<T1, T2>(std::move(f), f0, *l1));
    }
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, std::pair<T1, T2>>
  static T3 curry(F0 &&f, const T1 &a, const T2 &b) {
    return f(std::make_pair(a, b));
  }
};

struct CallableOps {
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static CallableConstraintCategories::lst<T2>
  map(F0 &&f, const CallableConstraintCategories::lst<T1> &l) {
    if (std::holds_alternative<
            typename CallableConstraintCategories::lst<T1>::Nil>(l.v())) {
      return CallableConstraintCategories::template lst<T2>::nil();
    } else {
      const auto &[a0, l0] =
          std::get<typename CallableConstraintCategories::lst<T1>::Cons>(l.v());
      return CallableConstraintCategories::template lst<T2>::cons(
          f(a0), map<T1, T2>(f, *l0));
    }
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T2 &&, const T1 &>
  static T2 foldl(F0 &&f, T2 acc,
                  const CallableConstraintCategories::lst<T1> &l) {
    if (std::holds_alternative<
            typename CallableConstraintCategories::lst<T1>::Nil>(l.v())) {
      return acc;
    } else {
      const auto &[a0, l0] =
          std::get<typename CallableConstraintCategories::lst<T1>::Cons>(l.v());
      return foldl<T1, T2>(f, f(std::move(acc), a0), *l0);
    }
  }
};

#endif // INCLUDED_CALLABLE_CONSTRAINT_CATEGORIES
