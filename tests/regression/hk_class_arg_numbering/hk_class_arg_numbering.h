#ifndef INCLUDED_HK_CLASS_ARG_NUMBERING
#define INCLUDED_HK_CLASS_ARG_NUMBERING

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <utility>
#include <variant>

struct Monad_option;
struct Nat;
template <typename I>
concept Functor = requires {
  typename I::template F<crane::obj>;
  {
    I::fmap(std::declval<crane::fn<crane::obj(crane::obj)>>(),
            std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
};
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

struct HkClassArgNumbering {
  static std::optional<Nat> use(const Nat &n);
};

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
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
  template <Monad _tcI0, typename T2, typename T3>
  static typename _tcI0::template m<T3>
  liftM(std::type_identity_t<crane::fn<T3(T2)>> f,
        typename _tcI0::template m<T2> x);
};

template <Monad _tcI0> struct Functor_Monad {
  template <typename CraneA0> using m = typename _tcI0::template m<CraneA0>;
  template <typename CraneA0> using F = typename _tcI0::template m<CraneA0>;

  static typename _tcI0::template m<crane::obj>
  fmap(crane::fn<crane::obj(crane::obj)> a0,
       typename _tcI0::template m<crane::obj> a1) {
    return Monad0::template liftM<_tcI0, crane::obj, crane::obj>(std::move(a0),
                                                                 std::move(a1));
  }
};

struct Monad_option {
  template <typename CraneA0> using m = std::optional<CraneA0>;

  template <typename CraneA0> static std::optional<CraneA0> ret(CraneA0 x) {
    return std::make_optional<CraneA0>(std::move(x));
  }

  template <typename CraneA0, typename CraneA1>
  static std::optional<CraneA1>
  bind(std::optional<CraneA0> c1,
       crane::fn<std::optional<CraneA1>(CraneA0)> c2) {
    if (c1.has_value()) {
      const CraneA0 &v = *c1;
      return c2(v);
    } else {
      return std::optional<CraneA1>();
    }
  }
};

static_assert(Monad<Monad_option>);
template <typename m>
using Iter = crane::fn<m(crane::fn<m(crane::obj)>, crane::obj)>;

template <typename T1, typename T2, typename F1>
crane::rebind_t<T1, T2> iter(std::type_identity_t<Iter<T1>> iter0, F1 &&x,
                             const T2 &x0) {
  return crane_container_cast<crane::rebind_t<T1, T2>>(
      iter0(crane_erase_fn<T1>(x), x0));
}

template <Functor _tcI0, Monad _tcI1, typename T2, typename F1>
typename _tcI0::template F<T2>
run(Iter<typename _tcI0::template F<crane::obj>> x0_, F1 &&x1_, const T2 &x2_) {
  return iter<typename _tcI0::template F<crane::obj>, T2>(std::move(x0_), x1_,
                                                          x2_);
}

template <typename F0>
std::optional<crane::obj> Iter_option(F0 &&f, crane::obj x0_) {
  return f(x0_);
}

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

template <Monad _tcI0, typename T2, typename T3>
typename _tcI0::template m<T3>
Monad0::liftM(std::type_identity_t<crane::fn<T3(T2)>> f,
              typename _tcI0::template m<T2> x) {
  return Monad0::template bind<_tcI0, T2, T3>(std::move(x), [=](const T2 &x0) {
    return Monad0::template ret<_tcI0, T3>(f(x0));
  });
}

#endif // INCLUDED_HK_CLASS_ARG_NUMBERING
