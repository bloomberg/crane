#ifndef INCLUDED_ERROR_CTOR_THROUGH_REIFIED_INSTANCE
#define INCLUDED_ERROR_CTOR_THROUGH_REIFIED_INSTANCE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct EOU;
struct EOU_monad;
struct Dv;
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

struct PeanoNat {
  static bool eqb(const Nat &n, const Nat &m);
};

template <typename A> struct EOU {
  // TYPES
  struct Ok {
    A a0;
  };

  struct Err {
    Nat a0;
  };

  using variant_t = std::variant<Ok, Err>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Ok _v) : v_(std::move(_v)) {}

  explicit EOU(Err _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  EOU(const EOU<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename EOU<CraneU>::Ok>(_other.v())) {
            const auto &[a0] = std::get<typename EOU<CraneU>::Ok>(_other.v());
            return Ok{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0] = std::get<typename EOU<CraneU>::Err>(_other.v());
            return Err{a0};
          }
        }()) {}

  static EOU<A> ok(A a0) { return EOU<A>(Ok{std::move(a0)}); }

  static EOU<A> err(Nat a0) { return EOU<A>(Err{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU_monad {
  template <typename CraneA0> using m = EOU<CraneA0>;

  template <typename CraneA0> static EOU<CraneA0> ret(CraneA0 a) {
    return EOU<CraneA0>::ok(std::move(a));
  }

  template <typename CraneA0, typename CraneA1>
  static EOU<CraneA1> bind(EOU<CraneA0> m, crane::fn<EOU<CraneA1>(CraneA0)> k) {
    if (std::holds_alternative<typename EOU<CraneA0>::Ok>(m.v())) {
      const auto &[a0] = std::get<typename EOU<CraneA0>::Ok>(m.v());
      return k(a0);
    } else {
      const auto &[a0] = std::get<typename EOU<CraneA0>::Err>(m.v());
      return EOU<CraneA1>::err(a0);
    }
  }
};

static_assert(Monad<EOU_monad>);

struct Dv {
  // TYPES
  struct DvBool {
    bool a0;
  };

  struct DvNat {
    Nat a0;
  };

  using variant_t = std::variant<DvBool, DvNat>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Dv() {}

  explicit Dv(DvBool _v) : v_(std::move(_v)) {}

  explicit Dv(DvNat _v) : v_(std::move(_v)) {}

  static Dv dvbool(bool a0) { return Dv(DvBool{a0}); }

  static Dv dvnat(Nat a0) { return Dv(DvNat{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct ErrorCtorThroughReifiedInstance {
  static EOU<Dv> eval_icmp(const Nat &x, const Nat &y);
  static inline const Nat run = []() {
    auto &&_sv = eval_icmp(Nat::s(Nat::o()), Nat::s(Nat::o()));
    if (std::holds_alternative<typename EOU<Dv>::Ok>(_sv.v())) {
      const auto &[a0] = std::get<typename EOU<Dv>::Ok>(_sv.v());
      if (std::holds_alternative<typename Dv::DvBool>(a0.v())) {
        const auto &[a00] = std::get<typename Dv::DvBool>(a0.v());
        if (a00) {
          return Nat::s(Nat::o());
        } else {
          return Nat::o();
        }
      } else {
        return Nat::o();
      }
    } else {
      return Nat::o();
    }
  }();
};

#endif // INCLUDED_ERROR_CTOR_THROUGH_REIFIED_INSTANCE
