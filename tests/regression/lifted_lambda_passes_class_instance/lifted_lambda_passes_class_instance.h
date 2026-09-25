#ifndef INCLUDED_LIFTED_LAMBDA_PASSES_CLASS_INSTANCE
#define INCLUDED_LIFTED_LAMBDA_PASSES_CLASS_INSTANCE

#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

struct Nat;
template <typename addr> struct Box;
struct natParams;

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

template <typename
I>concept Params = requires {
  typename I::addr;
  { I::bump(std::declval<typename I::addr>()) } -> std::convertible_to<typename I::addr>;
} && (requires {
  { I::zero() } -> std::convertible_to<typename I::addr>;
} || requires {
  { I::zero } -> std::convertible_to<typename I::addr>;
});
using addr = std::any;

template <typename addr> struct Box {
  // DATA
  addr a0;

  // ACCESSORS
  Box<addr> clone() const { return {a0}; }

  template <typename _U> operator Box<_U>() const { return {a0}; }

  // CREATORS
  static Box<addr> box0(addr a0) { return {std::move(a0)}; }
};

/// step is let-bound, {e polymorphic} in its own A --- which is what
/// sends it down the lift path rather than out as a std::function --- and
/// the class instance is free in its body.  Vellvm's
/// _denote_exp_denote_exp_base has exactly this shape: its own typename
/// T1 on top of the enclosing Params _tcI0.
template <Params _tcI0, typename T1>
auto _walk_step(const T1, const typename _tcI0::addr x) {
  return Box<typename _tcI0::addr>::box0(_tcI0::bump(x));
}

template <Params _tcI0>
Box<typename _tcI0::addr> walk(const Nat &n, const typename _tcI0::addr &a) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return _walk_step<_tcI0>(Nat::o(), a);
  } else {
    return _walk_step<_tcI0>(true, _tcI0::bump(std::move(a)));
  }
}

struct natParams {
  using addr = Nat;

  static Nat zero() { return Nat::o(); }

  static Nat bump(Nat x) { return Nat::s(std::move(x)); }
};

static_assert(Params<natParams>);

struct LiftedLambdaPassesClassInstance {
  static inline const Box<typename natParams::addr> run =
      walk<natParams>(Nat::s(Nat::o()), Nat::o());
};

#endif // INCLUDED_LIFTED_LAMBDA_PASSES_CLASS_INSTANCE
