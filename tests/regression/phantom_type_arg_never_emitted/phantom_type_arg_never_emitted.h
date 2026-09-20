#ifndef INCLUDED_PHANTOM_TYPE_ARG_NEVER_EMITTED
#define INCLUDED_PHANTOM_TYPE_ARG_NEVER_EMITTED

#include "small_vector.h"
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

/// phantom A does not store an A, so nothing in the program's *values*
/// ever mentions bool.  The call site still spells the instantiation
/// phantom<Bool0>, but dependency collection only walks value positions, so
/// the Bool0 enum is never emitted: "use of undeclared identifier
/// 'Bool0'".  Anything else in the module that mentions bool in a value
/// position hides the bug, which is why this test computes with nat only.
struct PhantomTypeArgNeverEmitted {
  template <typename A> struct phantom {
    // DATA
    Nat a0;

    // ACCESSORS
    phantom<A> clone() const { return {a0}; }

    template <typename _U> operator phantom<_U>() const { return {a0}; }

    // CREATORS
    static phantom<A> ph(Nat a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, Nat &>
  static T2 phantom_rect(F0 &&f, const phantom<T1> &p) {
    const auto &[a0] = p;
    return f(a0);
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, Nat &>
  static T2 phantom_rec(F0 &&f, const phantom<T1> &p) {
    const auto &[a0] = p;
    return f(a0);
  }

  template <typename T1> static Nat get(const phantom<T1> &p) {
    const auto &[a0] = p;
    return a0;
  }

  static inline const Nat run =
      get<Bool0>(phantom<Bool0>::ph(Nat::s(Nat::s(Nat::s(Nat::o())))));
};

#endif // INCLUDED_PHANTOM_TYPE_ARG_NEVER_EMITTED
