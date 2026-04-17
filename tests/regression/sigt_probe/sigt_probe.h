#ifndef INCLUDED_SIGT_PROBE
#define INCLUDED_SIGT_PROBE

#include <any>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_x;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<SigT<t_A, t_P>> existt(t_A x, t_P a1) {
    return std::make_shared<SigT<t_A, t_P>>(
        ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct SigTProbe {
  /// A dependent pair whose first component is a type and whose second
  /// component has that concrete type.  Regression test for the bug where
  /// Crane would generate SigT<std::any, Bool0> for the constructor call
  /// but declare the type as SigT<std::any, std::any>, producing
  /// incompatible shared_ptr template instantiations.
  static inline const std::shared_ptr<SigT<std::any, std::any>> packed =
      SigT<std::any, std::any>::existt(std::any{}, Bool0::e_TRUE0);
  static inline const std::shared_ptr<Nat> sample = Nat::o();
};

#endif // INCLUDED_SIGT_PROBE
