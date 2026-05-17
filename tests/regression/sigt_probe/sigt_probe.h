#ifndef INCLUDED_SIGT_PROBE
#define INCLUDED_SIGT_PROBE

#include <any>
#include <memory>
#include <utility>
#include <variant>
#include <vector>

enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> a0;
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

  Nat(const Nat &_other) : v_(std::move(_other.clone().v_)) {}

  Nat(Nat &&_other) : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->v_ = S{_alt.a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_unique<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A, typename P> struct SigT {
  // TYPES
  struct ExistT {
    A x;
    P a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  SigT() {}

  explicit SigT(ExistT _v) : v_(std::move(_v)) {}

  SigT(const SigT<A, P> &_other) : v_(std::move(_other.clone().v_)) {}

  SigT(SigT<A, P> &&_other) : v_(std::move(_other.v_)) {}

  SigT<A, P> &operator=(const SigT<A, P> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  SigT<A, P> &operator=(SigT<A, P> &&_other) {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  SigT<A, P> clone() const {
    const auto &[x, a1] = std::get<ExistT>(this->v());
    return SigT<A, P>(ExistT{x, a1});
  }

  // CREATORS
  template <typename _U0, typename _U1>
  explicit SigT(const SigT<_U0, _U1> &_other) {
    const auto &[x, a1] = std::get<typename SigT<_U0, _U1>::ExistT>(_other.v());
    this->v_ = ExistT{A(x), P(a1)};
  }

  static SigT<A, P> existt(A x, P a1) {
    return SigT(ExistT{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct SigTProbe {
  /// A dependent pair whose first component is a type and whose second
  /// component has that concrete type.  Regression test for the bug where
  /// Crane would generate SigT<std::any, Bool0> for the constructor call
  /// but declare the type as SigT<std::any, std::any>, producing
  /// incompatible shared_ptr template instantiations.
  static inline const SigT<std::any, std::any> packed =
      SigT<std::any, std::any>::existt(std::any{}, Bool0::TRUE_);
  static inline const Nat sample = Nat::o();
};

#endif // INCLUDED_SIGT_PROBE
