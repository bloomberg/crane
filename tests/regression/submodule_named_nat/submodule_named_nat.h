#ifndef INCLUDED_SUBMODULE_NAMED_NAT
#define INCLUDED_SUBMODULE_NAMED_NAT

#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Nat;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<::Nat> a0;
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

  static ::Nat o() { return ::Nat(O{}); }

  static ::Nat s(::Nat a0) {
    return ::Nat(S{std::make_shared<::Nat>(std::move(a0))});
  }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<::Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<::Nat> _cur = _next(v_mut());
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

struct SubmoduleNamedNat {
  /// A submodule named Nat becomes a nested struct that shadows the runtime
  /// Nat for every unqualified lookup inside its parent, so the runtime type
  /// must be spelled ::Nat:
  ///
  /// ::Nat SubmoduleNamedNat::Nat::succ(::Nat n)
  ///
  /// Unlike shadow_runtime_nat, the shadowing name here is a *module*, which
  /// carries no GlobRef.t of its own.
  struct Nat {
    static ::Nat succ(const ::Nat &n);
  };

  static ::Nat run(const ::Nat &x0_);
};

#endif // INCLUDED_SUBMODULE_NAMED_NAT
