#ifndef INCLUDED_TERNARY_OF_TWO_LAMBDAS
#define INCLUDED_TERNARY_OF_TWO_LAMBDAS

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
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
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

  Nat mul(const Nat &m) const {
    const Nat *_self = this;

    // Explicit stack replaces the non-tail recursion of mul: _call frames are
    // pending calls, _after frames resume a caller.
    struct _call {
      const Nat *_self;
    };

    struct _after_mul_in_S {};

    using _frame = std::variant<_call, _after_mul_in_S>;
    Nat _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame _popped = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        const Nat *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Nat::O>(_sv.v())) {
          _result = Nat::o();
        } else {
          const auto &[a0] = std::get<typename Nat::S>(_sv.v());
          _stack.emplace_back(_after_mul_in_S{});
          _stack.emplace_back(_call{crane_raw(a0)});
        }
      } else {
        auto _f = std::move(std::get<_after_mul_in_S>(_popped));
        _result = m.add(std::move(_result));
      }
    }
    return _result;
  }

  Nat add(Nat m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<Nat> _root{};
    std::shared_ptr<Nat> *_write = nullptr;
    const Nat *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        auto _value = std::move(m);
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

struct PeanoNat {
  static bool even(const Nat &n);
};

Nat f_even(const Nat &x0_, Nat x1_);
Nat f_odd(const Nat &x0_, const Nat &x1_);
/// Point-free: the body is an if whose branches are functions, and no
/// argument is written.
Nat pick(const Nat &n, Nat x0_);
Nat go(const Nat &x0_, Nat x1_);

#endif // INCLUDED_TERNARY_OF_TWO_LAMBDAS
