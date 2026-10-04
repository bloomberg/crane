#ifndef INCLUDED_SIBLING_MODULE_SAME_INDUCTIVE
#define INCLUDED_SIBLING_MODULE_SAME_INDUCTIVE

#include <atomic>
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

struct SiblingModuleSameInductive {
  /// Two sibling submodules each declare an inductive named t.  Both are
  /// nested structs, so neither shadows a global-scope t; the out-of-line
  /// definitions must stay plainly qualified:
  ///
  /// Nat SiblingModuleSameInductive::A::get(
  /// const SiblingModuleSameInductive::A::t &x)
  struct A {
    struct t {
      // DATA
      Nat a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t mk(Nat a0) { return {std::move(a0)}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Nat &>
    static T1 t_rect(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, Nat &>
    static T1 t_rec(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }

    static Nat get(const t &x);
  };

  struct B {
    struct t {
      // DATA
      bool a0;

      // ACCESSORS
      t clone() const { return {a0}; }

      // CREATORS
      static t mk(bool a0) { return {a0}; }
    };

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, bool &>
    static T1 t_rect(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, bool &>
    static T1 t_rec(F0 &&f, const t &t0) {
      const auto &[a0] = t0;
      return f(a0);
    }

    static bool get(const t &x);
  };

  static Nat run(const Nat &n);
  static bool run2(bool b);
};

#endif // INCLUDED_SIBLING_MODULE_SAME_INDUCTIVE
