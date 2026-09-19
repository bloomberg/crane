#ifndef INCLUDED_RANK3_HANDLER
#define INCLUDED_RANK3_HANDLER

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0;
struct Nat;
template <typename A> struct Option;
template <typename X> struct ReqA;
enum class Bool0 { TRUE_, FALSE_ };

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

  template <typename _U> Option(const Option<_U> &_other) {
    if (std::holds_alternative<typename Option<_U>::Some>(_other.v())) {
      const auto &[a] = std::get<typename Option<_U>::Some>(_other.v());
      this->v_ = Some{[&]() -> A {
        if constexpr (std::is_same_v<_U, std::any>) {
          return crane_any_cast<A>(a);
        } else {
          if constexpr (std::is_constructible_v<A, const _U &>) {
            return A(a);
          } else {
            throw std::logic_error("unreachable: inactive constructor field at "
                                   "this instantiation");
          }
        }
      }()};
    } else {
      this->v_ = None{};
    }
  }

  static Option<A> some(A a) { return Option<A>(Some{std::move(a)}); }

  static Option<A> none() { return Option<A>(None{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Polymorphism of rank three: a handler polymorphic in its own type
/// argument, a consumer that applies such a handler at two different types,
/// and a function that hands a handler to such a consumer.
///
/// Each rank-2 argument is extracted as a polymorphic function object -- a
/// lambda with its own template <typename> -- because no single
/// instantiation would do: useTwice applies the same handler at nat and
/// at bool.
template <typename X> struct ReqA {
  // DATA
  X a0;

  // ACCESSORS
  ReqA<X> clone() const { return {a0}; }

  // CREATORS
  static ReqA<X> mka(X a0) { return {std::move(a0)}; }
};

/// Rank 2: applies its handler at two types, so a monomorphic argument could
/// not stand in for it.
template <typename F0> Option<Nat> useTwice(F0 &&f) {
  auto &&_sv = f(ReqA<Nat>::mka(
      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))))));
  if (std::holds_alternative<typename Option<Nat>::Some>(_sv.v())) {
    const auto &[a0] = std::get<typename Option<Nat>::Some>(_sv.v());
    auto &&_sv0 = f(ReqA<Bool0>::mka(Bool0::TRUE_));
    if (std::holds_alternative<typename Option<Bool0>::Some>(_sv0.v())) {
      const auto &[a00] = std::get<typename Option<Bool0>::Some>(_sv0.v());
      switch (a00) {
      case Bool0::TRUE_: {
        return Option<Nat>::some(a0);
      }
      case Bool0::FALSE_: {
        return Option<Nat>::none();
      }
      default:
        std::unreachable();
      }
    } else {
      return Option<Nat>::none();
    }
  } else {
    return Option<Nat>::none();
  }
}

/// Rank 3: its own argument takes a handler.
template <typename F0> Option<Nat> runWith(F0 &&k) {
  return k([]<typename _X>(const ReqA<_X> &a) {
    const auto &[a0] = a;
    return Option<_X>::some(a0);
  });
}

/// The same rank-3 shape at another result type: the handler runWith2
/// supplies is the same polymorphic function object, and only the consumer's
/// result differs.
template <typename F0> Option<Bool0> runWith2(F0 &&k) {
  return k([]<typename _X>(const ReqA<_X> &a) {
    const auto &[a0] = a;
    return Option<_X>::some(a0);
  });
}

const Option<Nat> top = runWith([](auto &&_ec0) { return useTwice(_ec0); });

#endif // INCLUDED_RANK3_HANDLER
