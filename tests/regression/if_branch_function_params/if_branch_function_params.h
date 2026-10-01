#ifndef INCLUDED_IF_BRANCH_FUNCTION_PARAMS
#define INCLUDED_IF_BRANCH_FUNCTION_PARAMS

#include "crane_fn.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0;
struct Nat;
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

/// An if whose two branches are two *different* function-typed parameters is
/// emitted as an immediately-invoked lambda with a deduced return type.  The
/// two return statements hand back two distinct closure types, so deduction
/// reports conflicting types.  Returning the same function in both branches,
/// or one branch returning a literal lambda, happens to work; two different
/// binders do not.
struct IfBranchFunctionParams {
  template <typename F1, typename F2>
    requires std::is_invocable_r_v<Nat, F1 &, Nat &> &&
             std::is_invocable_r_v<Nat, F2 &, Nat &>
  static Nat h(Bool0 b, F1 &&f, F2 &&g, Nat x0_) {
    switch (b) {
    case Bool0::TRUE_: {
      return f(std::move(x0_));
    }
    case Bool0::FALSE_: {
      return g(std::move(x0_));
    }
    default:
      std::unreachable();
    }
  }

  static inline const Nat run = h(
      Bool0::FALSE_, [](const Nat &x) { return Nat::s(x); },
      [](const Nat &x) { return x.add(Nat::s(Nat::s(Nat::o()))); },
      Nat::s(Nat::o()));
};

#endif // INCLUDED_IF_BRANCH_FUNCTION_PARAMS
