#ifndef INCLUDED_CROSS_FILE_MODULE_REF
#define INCLUDED_CROSS_FILE_MODULE_REF

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <type_traits>
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

template <typename M>
concept S = requires {
  typename M::t;
  requires(
      requires {
        { M::zero } -> std::convertible_to<typename M::t>;
      } ||
      requires {
        { M::zero() } -> std::convertible_to<typename M::t>;
      });
};

template <S X> struct F {
  template <typename F0>
    requires std::is_invocable_r_v<typename X::t, F0 &, typename X::t &>
  static typename X::t twice(F0 &&f) {
    return f(f(X::zero));
  }
};

using M = F<Ord>;

struct Lib2 {
  static Nat bump(Nat n);
};

struct Ord {
  using t = Nat;
  static inline const t zero = Nat::o();
};

Nat bump0(Nat n);

struct CrossFileModuleRef {
  static inline const Nat use = M::twice(bump0).add(Lib2::bump(Nat::o()));
};

#endif // INCLUDED_CROSS_FILE_MODULE_REF
