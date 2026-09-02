#ifndef INCLUDED_SUBMODULE_NAMED_NAT
#define INCLUDED_SUBMODULE_NAMED_NAT

#include "small_vector.h"
#include <atomic>
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

struct SubmoduleNamedNat {
  /// A submodule named Nat collides with the runtime Nat struct.  Inside the
  /// generated struct Nat, the unqualified return type Nat resolves to the
  /// submodule rather than to the global inductive:
  ///
  /// error: return type of out-of-line definition of
  /// 'SubmoduleNamedNat::Nat::succ' differs from that in the declaration
  /// error: no member named 's' in 'SubmoduleNamedNat::Nat'
  ///
  /// Unlike shadow_runtime_nat, the shadowing name here is a *module*, so the
  /// fix has to qualify references from inside module scopes too.
  struct Nat {
    static Nat succ(Nat n);
  };

  static Nat run(const Nat &_x0);
};

#endif // INCLUDED_SUBMODULE_NAMED_NAT
