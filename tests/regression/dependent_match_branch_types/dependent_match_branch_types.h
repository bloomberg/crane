#ifndef INCLUDED_DEPENDENT_MATCH_BRANCH_TYPES
#define INCLUDED_DEPENDENT_MATCH_BRANCH_TYPES

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Unit;
struct Nat;
enum class Unit { TT };

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

/// A match with a return clause computing a *different* type per branch is
/// given one C++ return type for all branches — the one the use site wants.
/// The vnil branch returns tt, whose type is unit, and clang rejects "no
/// viable conversion from returned value of type 'Unit' to function return
/// type 'Nat'".  Dependent matches whose branches agree on a type extract
/// fine.
struct DependentMatchBranchTypes {
  struct vec {
    // TYPES
    struct Vnil {};

    struct Vcons {
      Nat n;
      Nat a1;
      std::shared_ptr<vec> a2;
    };

    using variant_t = std::variant<Vnil, Vcons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    vec() {}

    explicit vec(Vnil _v) : v_(_v) {}

    explicit vec(Vcons _v) : v_(std::move(_v)) {}

    static vec vnil() { return vec(Vnil{}); }

    static vec vcons(Nat n, Nat a1, vec a2) {
      return vec(Vcons{std::move(n), std::move(a1),
                       std::make_shared<vec>(std::move(a2))});
    }

    // MANIPULATORS
    ~vec() {
      crane::small_vector<std::shared_ptr<vec>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Vcons>(&_v)) {
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
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

    vec(const vec &) = default;
    vec &operator=(const vec &) = default;
    vec(vec &&) noexcept = default;
    vec &operator=(vec &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Nat &, Nat &, vec &, T1 &>
  static T1 vec_rect(T1 f, F1 &&f0, const Nat &, const vec &v) {
    if (std::holds_alternative<typename vec::Vnil>(v.v())) {
      return f;
    } else {
      const auto &[n1, a1, a2] = std::get<typename vec::Vcons>(v.v());
      return f0(n1, a1, *a2, vec_rect<T1>(std::move(f), f0, n1, *a2));
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, Nat &, Nat &, vec &, T1 &>
  static T1 vec_rec(T1 f, F1 &&f0, const Nat &, const vec &v) {
    if (std::holds_alternative<typename vec::Vnil>(v.v())) {
      return f;
    } else {
      const auto &[n1, a1, a2] = std::get<typename vec::Vcons>(v.v());
      return f0(n1, a1, *a2, vec_rec<T1>(std::move(f), f0, n1, *a2));
    }
  }

  static Nat hd(const Nat &_x, const vec &v);
  static inline const Nat run =
      hd(Nat::o(),
         vec::vcons(
             Nat::o(),
             Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))),
             vec::vnil()));
};

#endif // INCLUDED_DEPENDENT_MATCH_BRANCH_TYPES
