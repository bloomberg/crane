#ifndef INCLUDED_HKT_SINGLE_CTOR_INSTANCE_BODY
#define INCLUDED_HKT_SINGLE_CTOR_INSTANCE_BODY

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <utility>
#include <variant>

struct Nat;

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
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// A single-constructor inductive is generated as a plain struct with no
/// variant_t and no v().  An instance method whose body pattern-matches on
/// it is still emitted in variant style, against the erased carrier:
///
/// error: use of undeclared identifier 'Mkbox'
/// error: no member named 'v' in 'box<std::any>'
template <typename I>
concept Ftor = requires {
  typename I::template F<std::any>;
  {
    I::fmap(std::declval<std::function<std::any(std::any)>>(),
            std::declval<typename I::template F<std::any>>())
  } -> std::convertible_to<typename I::template F<std::any>>;
};
template <typename I>
concept Pointed = requires {
  typename I::template F<std::any>;
  {
    I::template pnt<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template F<std::any>>;
};

struct HktSingleCtorInstanceBody {
  template <Pointed _tcI0, Ftor _tcI1, typename T2>
  static typename _tcI1::template F<T2> pnt(const T2 &x) {
    return _tcI0::template pnt<T2>(x);
  }

  template <typename A> struct box {
    // DATA
    A a0;

    // ACCESSORS
    box<A> clone() const { return {a0}; }

    // CREATORS
    static box<A> mkbox(A a0) { return {std::move(a0)}; }
  };

  struct FB {
    template <typename _A0> using F = box<_A0>;

    static box<std::any> fmap(std::function<std::any(std::any)> f,
                              box<std::any> b) {
      const auto &[a0] = b;
      return box<std::any>::mkbox(f(a0));
    }
  };

  static_assert(Ftor<FB>);

  struct PB {
    template <typename _A0> using F = box<_A0>;

    template <typename _A0> static box<_A0> pnt(_A0 x) {
      return box<_A0>::mkbox(x);
    }
  };

  static_assert(Pointed<PB>);

  template <Pointed _tcI0, Ftor _tcI1>
  static typename _tcI1::template F<Nat> liftme(const Nat &x2_) {
    return pnt<_tcI0, _tcI1, Nat>(x2_);
  }

  static box<Nat> run(const Nat &n);
};

#endif // INCLUDED_HKT_SINGLE_CTOR_INSTANCE_BODY
