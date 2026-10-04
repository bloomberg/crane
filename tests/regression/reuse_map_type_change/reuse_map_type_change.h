#ifndef INCLUDED_REUSE_MAP_TYPE_CHANGE
#define INCLUDED_REUSE_MAP_TYPE_CHANGE

#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "obj.h"
#include "rc.h"

/// Reuse bug: the Perceus reuse pass recycles a cell of the *input* type to
/// build a value of the *output* type.
///
/// For a type-changing map : (A -> B) -> lst A -> lst B, the cons arm
/// rebuilds lst B while the recycled cell belongs to lst A, so codegen
/// emits
///
/// return lst<T2>::cons__reuse(std::move(std::get<1>(l.v_mut()).a1), ...)
/// ^ crane::rc<lst<T1>>, parameter wants
/// crane::rc<lst<T2>>
///
/// and clang rejects it ("no viable conversion"). The types are not merely
/// inconvenient: lst<A> and lst<B> have different size, alignment and
/// destructor, so constructing one in the other's storage would be undefined
/// behaviour even if the token were castable. The reuse candidate search
/// never checks that the matched inductive and the rebuilt constructor agree
/// on their type arguments.
///
/// go1 (A = B = nat) compiles, so the failure needs a map that actually
/// changes the element type. Removing Set Crane Reuse. makes the file
/// compile.
struct ReuseMapTypeChange {
  template <typename A> struct lst {
    // TYPES
    struct Nil {};

    struct Cons {
      A a0;
      crane::rc<lst<A>> a1;
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
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename lst<CraneU>::Nil>(_other.v())) {
              return Nil{};
            } else {
              const auto &[a0, a1] =
                  std::get<typename lst<CraneU>::Cons>(_other.v());
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
                  (a1 ? crane::make_rc<lst<A>>(crane_convert<lst<A>>(*a1))
                      : nullptr)};
            }
          }()) {}

    static lst<A> nil() { return lst<A>(Nil{}); }

    static lst<A> cons(A a0, lst<A> a1) {
      return lst<A>(Cons{std::move(a0), crane::make_rc<lst<A>>(std::move(a1))});
    }

    static lst<A> cons_crane_reuse(crane::rc<lst<A>> _tok, A a0, lst<A> a1) {
      return lst<A>(Cons{std::move(a0), crane::make_rc_reusing<lst<A>>(
                                            std::move(_tok), std::move(a1))});
    }

    // MANIPULATORS
    ~lst() {
      auto _next = [&](variant_t &_v) -> crane::rc<lst<A>> {
        if (auto *_alt = std::get_if<Cons>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      crane::rc<lst<A>> _cur = _next(v_mut());
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
      const auto &[a0, a1] = std::get<typename lst<T1>::Cons>(l.v());
      return f0(a0, *a1, lst_rect<T1, T2>(std::move(f), f0, *a1));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T2 lst_rec(T2 f, F1 &&f0, const lst<T1> &l) {
    if (std::holds_alternative<typename lst<T1>::Nil>(l.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename lst<T1>::Cons>(l.v());
      return f0(a0, *a1, lst_rec<T1, T2>(std::move(f), f0, *a1));
    }
  }

  static lst<uint64_t> build(uint64_t n, lst<uint64_t> acc);
  static uint64_t suml(const lst<uint64_t> &l);

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &&>
  static lst<T2> mapl(F0 &&f, lst<T1> l) {
    if (std::holds_alternative<typename lst<T1>::Nil>(l.v_mut())) {
      return lst<T2>::nil();
    } else {
      auto &[a0, a1] = std::get<typename lst<T1>::Cons>(l.v_mut());
      return lst<T2>::cons(f(std::move(a0)), mapl<T1, T2>(f, *a1));
    }
  }

  static uint64_t go1(uint64_t n);
  static uint64_t go2(uint64_t n);
};

#endif // INCLUDED_REUSE_MAP_TYPE_CHANGE
