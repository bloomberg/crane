#ifndef INCLUDED_CONCEPT_NAME_WITH_PRIME
#define INCLUDED_CONCEPT_NAME_WITH_PRIME

#include "crane_fn.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <utility>
#include <variant>

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

  Bool0 eqb(const Nat &m) const {
    const Nat *_loop_self = this;
    const Nat *_loop_m = &m;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename Nat::O>(_sv.v())) {
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return Bool0::TRUE_;
        } else {
          return Bool0::FALSE_;
        }
      } else {
        const auto &[a0] = std::get<typename Nat::S>(_sv.v());
        if (std::holds_alternative<typename Nat::O>(_loop_m->v())) {
          return Bool0::FALSE_;
        } else {
          const auto &[a00] = std::get<typename Nat::S>(_loop_m->v());
          _loop_self = crane_raw(a0);
          _loop_m = crane_raw(a00);
        }
      }
    }
  }
};

template <typename M>
concept Ord_ = requires {
  typename M::t;
  {
    M::cmp(std::declval<typename M::t>(), std::declval<typename M::t>())
  } -> std::same_as<Bool0>;
};

struct ConceptNameWithPrime {
  struct NatOrd_ {
    using t = Nat;
    static Bool0 cmp(const Nat &x0_, const Nat &x1_);
  };

  template <Ord_ O> struct Use {
    static Bool0 same(typename O::t x0_, typename O::t x1_) {
      return O::cmp(x0_, x1_);
    }
  };

  using U = Use<NatOrd_>;
  static inline const Bool0 test = U::same(Nat::s(Nat::o()), Nat::s(Nat::o()));
};

#endif // INCLUDED_CONCEPT_NAME_WITH_PRIME
