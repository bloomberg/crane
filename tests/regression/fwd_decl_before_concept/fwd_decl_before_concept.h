#ifndef INCLUDED_FWD_DECL_BEFORE_CONCEPT
#define INCLUDED_FWD_DECL_BEFORE_CONCEPT

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
    I::template fmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
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

struct FwdDeclBeforeConcept {
  static std::optional<bool> use(const std::optional<Nat> &o);
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

struct Functor0 {
  template <Functor _tcI0, typename T2, typename T3, typename F0>
  static typename _tcI0::template F<T3> fmap(F0 &&x,
                                             typename _tcI0::template F<T2> x0);
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

struct Monad_option {
  template <typename CraneA0> using m = std::optional<CraneA0>;

  template <typename CraneA0> static std::optional<CraneA0> ret(CraneA0 x) {
    return std::make_optional<CraneA0>(x);
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

template <Monad _tcI0> struct Functor_Monad {
  template <typename CraneA0> using m = typename _tcI0::template m<CraneA0>;
  template <typename CraneA0> using F = typename _tcI0::template m<CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static typename _tcI0::template m<CraneA1>
  fmap(crane::fn<CraneA1(CraneA0)> f, typename _tcI0::template m<CraneA0> x) {
    return Monad0::template bind<_tcI0, CraneA0, CraneA1>(
        std::move(x), [=](const CraneA0 &a) {
          return Monad0::template ret<_tcI0, CraneA1>(f(a));
        });
  }
};

template <Functor _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template F<T3>
Functor0::fmap(F0 &&x, typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmap<T2, T3>(x, std::move(x0));
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

#endif // INCLUDED_FWD_DECL_BEFORE_CONCEPT
