#ifndef INCLUDED_INSTANCE_USE_DROPS_FAMILY_ARG
#define INCLUDED_INSTANCE_USE_DROPS_FAMILY_ARG

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A, typename B> struct Sum;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  bool eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return false;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
};

template <typename A, typename B> struct Sum {
  // TYPES
  struct Inl {
    A a0;
  };

  struct Inr {
    B a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sum() {}

  explicit Sum(Inl _v) : v_(std::move(_v)) {}

  explicit Sum(Inr _v) : v_(std::move(_v)) {}

  template <typename CraneU0, typename CraneU1>
  Sum(const Sum<CraneU0, CraneU1> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sum<CraneU0, CraneU1>::Inl>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inl>(_other.v());
            return Inl{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU0 &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] =
                std::get<typename Sum<CraneU0, CraneU1>::Inr>(_other.v());
            return Inr{[&]() -> B {
              if constexpr (crane_convertible<B, const CraneU1 &>) {
                return crane_convert<B>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Sum<A, B> inl(A a0) { return Sum<A, B>(Inl{std::move(a0)}); }

  static Sum<A, B> inr(B a0) { return Sum<A, B>(Inr{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I>
concept Monad = requires {
  typename I::template M<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template M<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template M<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
};

struct InstanceUseDropsFamilyArg {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template M<T2> ret(const T2 &x) {
    return _tcI0::template ret<T2>(x);
  }

  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template M<T3> bind(typename _tcI0::template M<T2> x,
                                             F1 &&x0) {
    return _tcI0::template bind<T2, T3>(std::move(x), x0);
  }

  template <typename E, typename A> struct box {
    // DATA
    A a;

    // ACCESSORS
    box<E, A> clone() const { return {a}; }

    template <typename CraneU0, typename CraneU1>
      requires crane_convertible<CraneU1, const A &>
    operator box<CraneU0, CraneU1>() const {
      return {crane_convert<CraneU1>(a)};
    }

    // CREATORS
    static box<E, A> box0(A a) { return {std::move(a)}; }
  };

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T2 &>
  static T3 box_rect(F0 &&f, const box<T1, T2> &b) {
    const auto &[a0] = b;
    return f(a0);
  }

  template <typename T1, typename T2, typename T3, typename F0>
    requires std::is_invocable_r_v<T3, F0 &, const T2 &>
  static T3 box_rec(F0 &&f, const box<T1, T2> &b) {
    const auto &[a0] = b;
    return f(a0);
  }

  template <typename T1> struct Monad_box {
    template <typename CraneA0> using M = box<T1, CraneA0>;

    template <typename CraneA0> static box<T1, CraneA0> ret(CraneA0 a) {
      return box<T1, CraneA0>::box0(std::move(a));
    }

    template <typename CraneA0, typename CraneA1>
    static box<T1, CraneA1> bind(box<T1, CraneA0> m,
                                 crane::fn<box<T1, CraneA1>(CraneA0)> k) {
      const auto &[a0] = m;
      return k(a0);
    }
  };

  template <typename P> struct aE {
    // DATA
    P a0;

    // ACCESSORS
    aE<P> clone() const { return {a0}; }

    template <typename CraneU>
      requires crane_convertible<CraneU, const P &>
    operator aE<CraneU>() const {
      return {crane_convert<CraneU>(a0)};
    }

    // CREATORS
    static aE<P> a(P a0) { return {std::move(a0)}; }
  };
  enum class BE { B };
  template <typename p, typename x = void> using AllE = Sum<aE<p>, BE>;
  template <typename p, typename x> using top = box<AllE<p, crane::obj>, x>;

  template <typename T1>
  static box<AllE<T1, crane::obj>, Nat> incr(const Nat &n) {
    return bind<Monad_box<AllE<T1, crane::obj>>, Nat, Nat>(
        ret<Monad_box<AllE<T1, crane::obj>>, Nat>(n), [](const Nat &m) {
          return ret<Monad_box<AllE<T1, crane::obj>>, Nat>(Nat::s(m));
        });
  }

  static inline const box<AllE<Nat, crane::obj>, Nat> r =
      incr<Nat>(Nat::s(Nat::s(Nat::o())));

  static constexpr bool is_three = true;
};

#endif // INCLUDED_INSTANCE_USE_DROPS_FAMILY_ARG
