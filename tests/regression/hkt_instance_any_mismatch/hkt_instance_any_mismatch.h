#ifndef INCLUDED_HKT_INSTANCE_ANY_MISMATCH
#define INCLUDED_HKT_INSTANCE_ANY_MISMATCH

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
template <typename A> struct Option;

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

template <typename A> struct Option {
  // TYPES
  struct Some {
    A a;
  };

  struct None {};

  using variant_t = std::variant<Some, None>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Option() {}

  explicit Option(Some _v) : v_(std::move(_v)) {}

  explicit Option(None _v) : v_(_v) {}

  template <typename CraneU>
  Option(const Option<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Option<CraneU>::Some>(
                  _other.v())) {
            const auto &[a] =
                std::get<typename Option<CraneU>::Some>(_other.v());
            return Some{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return None{};
          }
        }()) {}

  static Option<A> some(A a) { return Option<A>(Some{std::move(a)}); }

  static Option<A> none() { return Option<A>(None{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename I>
concept Mon = requires {
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

struct HktInstanceAnyMismatch {
  template <Mon _tcI0, typename T2>
  static typename _tcI0::template M<T2> ret(const T2 &x) {
    return _tcI0::template ret<T2>(x);
  }

  template <Mon _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template M<T3> bind(typename _tcI0::template M<T2> x,
                                             F1 &&x0) {
    return _tcI0::template bind<T2, T3>(std::move(x), x0);
  }

  struct optMon {
    template <typename CraneA0> using M = Option<CraneA0>;

    template <typename CraneA0> static Option<CraneA0> ret(CraneA0 a) {
      return Option<CraneA0>::some(std::move(a));
    }

    template <typename CraneA0, typename CraneA1>
    static Option<CraneA1> bind(Option<CraneA0> m,
                                crane::fn<Option<CraneA1>(CraneA0)> f) {
      if (std::holds_alternative<typename Option<CraneA0>::Some>(m.v())) {
        const auto &[a0] = std::get<typename Option<CraneA0>::Some>(m.v());
        return f(a0);
      } else {
        return Option<CraneA1>::none();
      }
    }
  };

  static_assert(Mon<optMon>);
  static inline const Option<Nat> test = optMon::template bind<Nat, Nat>(
      optMon::template ret<Nat>(Nat::s(Nat::o())),
      [](const Nat &n) { return optMon::template ret<Nat>(Nat::s(n)); });
};

#endif // INCLUDED_HKT_INSTANCE_ANY_MISMATCH
