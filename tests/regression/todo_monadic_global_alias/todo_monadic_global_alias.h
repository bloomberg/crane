#ifndef INCLUDED_TODO_MONADIC_GLOBAL_ALIAS
#define INCLUDED_TODO_MONADIC_GLOBAL_ALIAS

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        const auto &_alt = std::get<O>(_src->v());
        _dst->d_v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->d_v_ = S{_alt.d_a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->d_v_);
        if (_alt.d_a0)
          _stack.push_back({_alt.d_a0.get(), _dst_alt.d_a0.get()});
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_unique<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack;
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.d_v_)) {
        auto &_alt = std::get<S>(_node.d_v_);
        if (_alt.d_a0)
          _stack.push_back(std::move(_alt.d_a0));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
};

struct TodoMonadicGlobalAlias {
  static Nat base();
  static Nat alias();
  static Nat rebound();
};

#endif // INCLUDED_TODO_MONADIC_GLOBAL_ALIAS
