#ifndef INCLUDED_LOCAL_FIX_ESCAPES_BY_REF
#define INCLUDED_LOCAL_FIX_ESCAPES_BY_REF

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};

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

  List<A> rev_append(List<A> l_) const {
    const List<A> *_loop_self = this;
    List<A> _loop_l_ = std::move(l_);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_l_;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a1);
        _loop_l_ = List<A>::cons(a0, std::move(_loop_l_));
      }
    }
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

/// map_monad_acc (Vellvm's ListUtil.map_monad_acc) is a local fix
/// whose recursive call sits in a bind continuation.  Crane emitted the
/// fix as auto loop_impl = [&](auto &_self_loop, ...) { ... f(a0) ... }
/// and the continuation as [=](T3 b) { return _self_loop(_self_loop, ...);
/// }, which copied loop_impl -- still holding f and the enclosing frame
/// {e by reference} -- into a closure that escapes.  In a state monad the
/// bind does not run the continuation; it returns a function of the state,
/// which is called after map_monad_acc has returned, by when f is a
/// dangling reference.  The fixpoint's escape analysis looked only at the
/// code after the fixpoint, never inside its own bodies, and not at all
/// when the fixpoint is applied where it is defined.  A self-call inside a
/// closure the fixpoint's body builds now makes the fixpoint capture by
/// value.
///
/// check alone can pass, because the dead frame is often still intact;
/// the test driver also builds the state function, overwrites the stack,
/// and only then runs it.
///
/// Found in Vellvm's mem-scan and alloca-churn (Memory1's state monad
/// memS).
struct LocalFixEscapesByRef {
  /// A record, like Vellvm's MemS: bind builds a new state function and
  /// returns it without running k.
  template <typename A> struct res {
    // DATA
    uint64_t s;
    A a;

    // ACCESSORS
    res<A> clone() const { return {s, a}; }

    template <typename CraneU> operator res<CraneU>() const {
      return {s, [&]() -> CraneU {
                if constexpr (crane_convertible<CraneU, const A &>) {
                  return crane_convert<CraneU>(a);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
    }

    // CREATORS
    static res<A> res0(uint64_t s, A a) { return {s, std::move(a)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const uint64_t &, const T1 &>
  static T2 res_rect(F0 &&f, const res<T1> &r) {
    const auto &[s0, a0] = r;
    return f(s0, a0);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const uint64_t &, const T1 &>
  static T2 res_rec(F0 &&f, const res<T1> &r) {
    const auto &[s0, a0] = r;
    return f(s0, a0);
  }

  template <typename A> struct st {
    crane::fn<res<A>(uint64_t)> runst;

    // ACCESSORS
    template <typename CraneU> operator st<CraneU>() const {
      return {crane_convert<crane::fn<res<CraneU>(uint64_t)>>(runst)};
    }
  };

  struct Monad_st {
    template <typename CraneA0> using m = st<CraneA0>;

    template <typename CraneA0> static st<CraneA0> ret(CraneA0 x) {
      return st<CraneA0>{
          [=](uint64_t s) { return res<crane::obj>::res0(s, x); }};
    }

    template <typename CraneA0, typename CraneA1>
    static st<CraneA1> bind(st<CraneA0> m, crane::fn<st<CraneA1>(CraneA0)> k) {
      return st<CraneA1>{[=](uint64_t s) {
        const auto &_sv = m.runst(s);
        const auto &[s0, a0] = _sv;
        return k(a0).runst(s0);
      }};
    }
  };

  static_assert(Monad<Monad_st>);

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<st<T2>, const F0 &, const T1 &>
  static st<List<T2>> map_monad_acc(F0 &&f, const List<T1> &l) {
    auto loop_impl = [=](auto &_self_loop, List<crane::obj> acc,
                         List<T1> l0) -> st<List<T2>> {
      if (std::holds_alternative<typename List<T1>::Nil>(l0.v())) {
        return Monad0::template ret<Monad_st, List<T2>>(
            acc.rev_append(List<T2>::nil()));
      } else {
        const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l0.v());
        const List<T1> &a1_value = *a1;
        return Monad0::template bind<Monad_st, T2, List<T2>>(
            f(a0), [=](const T2 &b) {
              return _self_loop(_self_loop, List<crane::obj>::cons(b, acc),
                                a1_value);
            });
      }
    };
    auto loop = [=](List<crane::obj> acc, List<T1> l0) -> st<List<T2>> {
      return loop_impl(loop_impl, acc, l0);
    };
    return loop(List<crane::obj>::nil(), l);
  }

  /// Each step doubles the element and counts one state tick.
  static res<List<uint64_t>> run(const List<uint64_t> &l);
  static bool check(std::monostate _x);
};

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_LOCAL_FIX_ESCAPES_BY_REF
