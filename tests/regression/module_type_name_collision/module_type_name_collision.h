#ifndef INCLUDED_MODULE_TYPE_NAME_COLLISION
#define INCLUDED_MODULE_TYPE_NAME_COLLISION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
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
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

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

  template <typename CraneU>
  Opt(const Opt<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Opt<CraneU>::None>(_other.v())) {
            return None{};
          } else {
            const auto &[x] = std::get<typename Opt<CraneU>::Some>(_other.v());
            return Some{[&]() -> X {
              if constexpr (crane_convertible<X, const CraneU &>) {
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
  template <typename CraneA0> using m = Opt<CraneA0>;

  template <typename CraneA0> static Opt<CraneA0> ret(CraneA0 x) {
    return Opt<CraneA0>::some(std::move(x));
  }

  template <typename CraneA0, typename CraneA1>
  static Opt<CraneA1> bind(Opt<CraneA0> c, crane::fn<Opt<CraneA1>(CraneA0)> k) {
    if (std::holds_alternative<typename Opt<CraneA0>::None>(c.v())) {
      return Opt<CraneA1>::none();
    } else {
      const auto &[x0] = std::get<typename Opt<CraneA0>::Some>(c.v());
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
typename _tcI0::template m<T3> Monad0::bind(typename _tcI0::template m<T2> x,
                                            F1 &&x0) {
  return _tcI0::template bind<T2, T3>(std::move(x), x0);
}

#endif // INCLUDED_MODULE_TYPE_NAME_COLLISION
