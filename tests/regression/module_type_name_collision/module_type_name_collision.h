#ifndef INCLUDED_MODULE_TYPE_NAME_COLLISION
#define INCLUDED_MODULE_TYPE_NAME_COLLISION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename X> struct Opt;
struct opt_monad;
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

struct ModuleTypeNameCollision {
  static Opt<Nat> use(const Nat &n);
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
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  Nat add(Nat m) const {
    std::shared_ptr<Nat> _head{};
    std::shared_ptr<Nat> *_write = &_head;
    const Nat *_loop_self = this;
    Nat _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        *_write = std::make_shared<Nat>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        auto _cell = std::make_shared<Nat>(typename Nat::S(nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename Nat::S>((*_write)->v_mut()).a0;
        _loop_self = crane_raw(a0);
        continue;
      }
    }
    return std::move(*_head);
  }
};

struct Monad0 {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template m<T2> ret(const T2 &x);
  template <Monad _tcI0, typename T2, typename T3, typename F1>
    requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
  static typename _tcI0::template m<T3> bind(typename _tcI0::template m<T2> x,
                                             F1 &&x0);
};

template <typename X> struct Opt {
  // TYPES
  struct None {};

  struct Some {
    X x;
  };

  using variant_t = std::variant<None, Some>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Opt() {}

  explicit Opt(None _v) : v_(_v) {}

  explicit Opt(Some _v) : v_(std::move(_v)) {}

  template <typename _U>
  Opt(const Opt<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Opt<_U>::None>(_other.v())) {
            return None{};
          } else {
            const auto &[x] = std::get<typename Opt<_U>::Some>(_other.v());
            return Some{[&]() -> X {
              if constexpr (crane_convertible<X, const _U &>) {
                return crane_convert<X>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          }
        }()) {}

  static Opt<X> none() { return Opt<X>(None{}); }

  static Opt<X> some(X x) { return Opt<X>(Some{std::move(x)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct opt_monad {
  template <typename _A0> using m = Opt<_A0>;

  template <typename _A0> static Opt<_A0> ret(_A0 x) {
    return Opt<_A0>::some(std::move(x));
  }

  template <typename _A0, typename _A1>
  static Opt<_A1> bind(Opt<_A0> c, crane::fn<Opt<_A1>(_A0)> k) {
    if (std::holds_alternative<typename Opt<_A0>::None>(c.v())) {
      return Opt<_A1>::none();
    } else {
      const auto &[x0] = std::get<typename Opt<_A0>::Some>(c.v());
      return k(x0);
    }
  }
};

static_assert(Monad<opt_monad>);
Opt<Nat> double0(const Nat &n);

template <Monad _tcI0, typename T2>
typename _tcI0::template m<T2> Monad0::ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Monad _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_MODULE_TYPE_NAME_COLLISION
