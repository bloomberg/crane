#ifndef INCLUDED_INSTANCE_IN_RECORD_LITERAL
#define INCLUDED_INSTANCE_IN_RECORD_LITERAL

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename X> struct EOU;
struct EOU_monad;
struct Ops_nat;
template <typename I>
concept Monad = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::bind(std::declval<typename I::template m<crane::obj>>(),
            std::declval<
                crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};
template <typename CraneInst, typename I>
concept Ops = requires {
  {
    CraneInst::madd(std::declval<I>(), std::declval<I>())
  } -> std::convertible_to<EOU<I>>;
  { CraneInst::mzero() } -> std::convertible_to<I>;
};

struct InstanceInRecordLiteral {
  static EOU<Nat> use(const Nat &n);
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

  Nat add(Nat m) const {
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(_loop_m);
        (_write ? *(*_write = std::make_shared<Nat>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = typename Nat::S(nullptr);
        Nat &_node =
            (_write ? *(*_write = std::make_shared<Nat>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename Nat::S>(_node.v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
};

template <typename X> struct EOU {
  // TYPES
  struct Raise_error {
    Nat s;
  };

  struct Raise_ret {
    X x;
  };

  using variant_t = std::variant<Raise_error, Raise_ret>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  EOU() {}

  explicit EOU(Raise_error _v) : v_(std::move(_v)) {}

  explicit EOU(Raise_ret _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  EOU(const EOU<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename EOU<CraneU>::Raise_error>(
                  _other.v())) {
            const auto &[s] =
                std::get<typename EOU<CraneU>::Raise_error>(_other.v());
            return Raise_error{s};
          } else {
            const auto &[x] =
                std::get<typename EOU<CraneU>::Raise_ret>(_other.v());
            return Raise_ret{[&]() -> X {
              if constexpr (crane_convertible<X, const CraneU &>) {
                return crane_convert<X>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static EOU<X> raise_error(Nat s) { return EOU<X>(Raise_error{std::move(s)}); }

  static EOU<X> raise_ret(X x) { return EOU<X>(Raise_ret{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EOU_monad {
  template <typename CraneA0> using m = EOU<CraneA0>;

  template <typename CraneA0> static EOU<CraneA0> ret(CraneA0 x) {
    return EOU<CraneA0>::raise_ret(std::move(x));
  }

  static EOU<crane::obj> bind(EOU<crane::obj> c,
                              crane::fn<EOU<crane::obj>(crane::obj)> k) {
    if (std::holds_alternative<typename EOU<crane::obj>::Raise_error>(c.v())) {
      const auto &[s0] = std::get<typename EOU<crane::obj>::Raise_error>(c.v());
      return EOU<crane::obj>::raise_error(s0);
    } else {
      const auto &[x0] = std::get<typename EOU<crane::obj>::Raise_ret>(c.v());
      return k(x0);
    }
  }
};

static_assert(Monad<EOU_monad>);

struct Ops_nat {
  static EOU<Nat> madd(Nat x, Nat y) {
    return EOU_monad::template ret<Nat>(x.add(std::move(y)));
  }

  static Nat mzero() { return Nat::o(); }
};

static_assert(Ops<Ops_nat, Nat>);

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

#endif // INCLUDED_INSTANCE_IN_RECORD_LITERAL
